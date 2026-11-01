"""Build an X-Plane custom scenery pack that draws exactly the obstacle set.

Every polygon in sf_buildings.json becomes a facade extruded to its height, and X-Plane's own
buildings, autogen and forests are excluded inside the obstacle box, so what X-Plane renders
there is the JSON and nothing else. Writes the DSF tile directly (no DSFTool needed).

Buildings are dressed like the photoreal renderer on main (flight/src/photo.rs): the same six CC0
facade textures and two roof textures from flight/assets/textures, picked per building by the same
height rule and the same seed, so the two views agree. Textures are read from the working tree or,
when this branch lacks them, from origin/main with git show. Per-building tint is not reproduced
(X-Plane facades cannot be tinted per instance).

usage: python3 -I sidecar/build_xplane_scenery.py [--xplane ~/X-Plane-12] [--buildings sidecar/sf_buildings.json]
       python3 -I sidecar/build_xplane_scenery.py --world flight/data/sf/sf_world.bin   # the bcbf filter's own city
       python3 -I sidecar/build_xplane_scenery.py --grid city-map/   # the gate's procedural city (Tools/city-export),
                                                                     # placed on the Bay by sidecar/gridmap.py, with its terrain
"""
import argparse
import hashlib
import sys
import json
import os
import math
import struct

PACK = "OSM Obstacles - SF Downtown"
GRID_PACK = "Grid City - Gate Map"
TERRAIN_OBJ = "objects/terrain.obj"
TILE = "+37-123"
# (name, columns, floors, glass) exactly as flight/src/assets.rs FACADES; floor height 3.6 m for the first three, 3.2 after.
FACADES = [("facade_glass", 16.0, 10.0), ("facade_grid", 14.0, 8.0), ("facade_office", 32.0, 32.0),
           ("facade_brick", 6.0, 6.0), ("facade_stone", 6.0, 6.0), ("facade_brown", 6.0, 6.0)]
ROOFS = ["gravel", "concrete"]
ROOF_TILE_M = 12.0
TEXTURE_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "flight", "assets", "textures")


def building_seed(x0, y0, lot):
    """photo.rs building_seed: fract(sin(x0*7.31 + y0*3.17 + lot*0.618) * 43758.5453)."""
    import math
    return abs(math.modf(math.sin(x0 * 7.31 + y0 * 3.17 + lot * 0.618) * 43758.5453)[0])


def facade_index(h, seed):
    """photo.rs building_mesh: wall set by height class and seed, roof by seed; returns index into the 12 .fac files."""
    pick = lambda opts: opts[int(seed * 977.0) % len(opts)]
    ft = pick([0, 1, 2, 0, 1]) if h > 70.0 else pick([1, 2, 3, 4, 5]) if h > 30.0 else pick([3, 4, 5])
    roof = 0 if math.modf(seed * 53.0)[0] < 0.55 else 1
    return ft * len(ROOFS) + roof


def facade_path(i):
    return f"facades/{FACADES[i // len(ROOFS)][0]}_{ROOFS[i % len(ROOFS)]}.fac"


def fac_text(ft, roof):
    name, cols, rows = FACADES[ft]
    tile = rows * (3.6 if ft < 3 else 3.2)       # the texture spans `rows` floors; it is square
    return f"""A
800
FACADE
SHADER_WALL
TEXTURE {name}.png
TWO_SIDED 0
SHADER_ROOF
TEXTURE {ROOFS[roof]}.png
TWO_SIDED 0
LOD 0 30000
TEX_SIZE 1024 1024
ROOF_SCALE 0 0 512 512 1024 1024 {ROOF_TILE_M} {ROOF_TILE_M}
TEX_SIZE 1024 1024
WALL 0 100000
ROOF_SLOPE 0
SCALE {tile:.3f} {tile:.3f}
LEFT 0 512
CENTER 512 1024
CENTER 0 512
RIGHT 512 1024
BOTTOM 0 512
MIDDLE 512 1024
MIDDLE 0 512
TOP 512 1024
"""


def texture_bytes(name):
    """albedo.jpg of a texture set, from the working tree or from origin/main."""
    import subprocess
    path = os.path.join(TEXTURE_DIR, name, "albedo.jpg")
    if os.path.exists(path):
        return open(path, "rb").read()
    return subprocess.check_output(["git", "show", f"origin/main:flight/assets/textures/{name}/albedo.jpg"],
                                   cwd=os.path.dirname(os.path.dirname(os.path.dirname(TEXTURE_DIR))))


def write_textures(fac_dir):
    from PIL import Image
    import io
    for name in [f[0] for f in FACADES] + ROOFS:
        img = Image.open(io.BytesIO(texture_bytes(name))).convert("RGB").resize((1024, 1024))
        img.save(os.path.join(fac_dir, name + ".png"), optimize=True)


def atom(aid, payload):
    return aid.encode()[::-1] + struct.pack("<I", 8 + len(payload)) + payload


def strings(items):
    return b"".join(s.encode() + b"\0" for s in items)


def ccw(poly):
    """Counter-clockwise ring (X-Plane's rule for exteriors), with no repeated closing point."""
    if poly[0] == poly[-1]:
        poly = poly[:-1]
    area = sum(poly[i][1] * poly[(i + 1) % len(poly)][0] - poly[(i + 1) % len(poly)][1] * poly[i][0]
               for i in range(len(poly)))   # in (lon, lat) order: x = lon, y = lat
    return poly if area > 0 else poly[::-1]


def build_dsf(buildings, bbox, terrain_at=None):
    """terrain_at: (lat, lon) to place objects/terrain.obj at (the grid city), or None."""
    south, west, north, east = bbox
    props = [("sim/west", "-123"), ("sim/east", "-122"), ("sim/north", "38"), ("sim/south", "37"),
             ("sim/planet", "earth"), ("sim/creation_agent", "vibecheck-tsa build_xplane_scenery"),
             ("sim/overlay", "1")]
    box = f"{west}/{south}/{east}/{north}"
    for key in ("sim/exclude_obj", "sim/exclude_fac", "sim/exclude_for", "sim/exclude_pol", "sim/exclude_str",
                "sim/exclude_lin"):
        props.append((key, box))
    props.append(("sim/require_facade", "1/0"))
    head = atom("HEAD", atom("PROP", strings(k for kv in props for k in kv)))
    defn = atom("DEFN", atom("TERT", b"") + atom("OBJT", strings([TERRAIN_OBJ]) if terrain_at else b"")
                + atom("POLY", strings(facade_path(i) for i in range(len(FACADES) * len(ROOFS))))
                + atom("NETW", b"") + atom("DEMN", b""))
    pools, scals, cmds = b"", b"", b""
    kept = 0
    if terrain_at:
        lat, lon = terrain_at
        pools += atom("POOL", struct.pack("<IB", 1, 3) + b"\0" + struct.pack("<H", 0) + b"\0" + struct.pack("<H", 0)
                      + b"\0" + struct.pack("<H", 0))
        scals += atom("SCAL", struct.pack("<ff", 1.0, lon) + struct.pack("<ff", 1.0, lat) + struct.pack("<ff", 360.0, 0.0))
        cmds += struct.pack("<BB", 3, 0) + struct.pack("<BH", 1, 0) + struct.pack("<BH", 7, 0)   # object 0, pool 0, OBJECT
        kept = 1
    current = None
    for b in sorted(buildings, key=lambda b: b.get("facade", 0)):
        if b.get("facade", 0) != current:
            current = b.get("facade", 0)
            cmds += struct.pack("<BB", 3, current)          # SET_DEFINITION8: this facade
        ring = ccw([(p[1], p[0]) for p in b["polygon"]])     # (lon, lat)
        if not 3 <= len(ring) <= 255:
            continue
        lons = [p[0] for p in ring]
        lats = [p[1] for p in ring]
        planes = []
        for vals in (lons, lats):
            lo, hi = min(vals), max(vals)
            span = max(hi - lo, 1e-6)
            planes.append((lo, span, [round((v - lo) / span * 65535) for v in vals]))
        pool = struct.pack("<IB", len(ring), 2)
        for lo, span, raw in planes:
            pool += b"\0" + struct.pack(f"<{len(raw)}H", *raw)
        pools += atom("POOL", pool)
        scals += atom("SCAL", b"".join(struct.pack("<ff", span, lo) for lo, span, _ in planes))
        h = max(1, min(65535, round(b["height_m"])))
        cmds += struct.pack("<BH", 1, kept)                 # POOL_SELECT
        cmds += struct.pack("<BHB", 12, h, len(ring)) + struct.pack(f"<{len(ring)}H", *range(len(ring)))  # POLYGON
        kept += 1
    body = b"XPLNEDSF" + struct.pack("<I", 1) + head + defn + atom("GEOD", pools + scals) + atom("CMDS", cmds)
    return body + hashlib.md5(body).digest(), kept


def read_sf_world(path):
    """The bcbf crate's collision world (flight/data/sf/sf_world.bin) as the same building list
    build_dsf takes: name, height above the crate's terrain, polygon in lat/lon."""
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))
    from bcbf import from_local
    b = open(path, "rb").read()
    assert b[:4] == b"SFW1" and struct.unpack_from("<I", b, 4)[0] == 1
    lon0, lat0, e0, n0, half = struct.unpack_from("<5d", b, 8)
    tn, tsp = struct.unpack_from("<If", b, 48)
    off = 56
    terr = struct.unpack_from(f"<{tn * tn}f", b, off)
    off += 4 * tn * tn

    def ground(x, y):   # bilinear on the tn x tn grid, rows south -> north
        fx, fy = (x + half) / tsp, (y + half) / tsp
        i, j = int(max(0, min(tn - 2, fx))), int(max(0, min(tn - 2, fy)))
        u, v = max(0.0, min(1.0, fx - i)), max(0.0, min(1.0, fy - j))
        z00, z10, z01, z11 = terr[j * tn + i], terr[j * tn + i + 1], terr[(j + 1) * tn + i], terr[(j + 1) * tn + i + 1]
        return (z00 * (1 - u) + z10 * u) * (1 - v) + (z01 * (1 - u) + z11 * u) * v

    n = struct.unpack_from("<I", b, off)[0]
    off += 4
    out = []
    for _ in range(n):
        z0, z1, kind, nv, _pad, group = struct.unpack_from("<ffBBHI", b, off)
        off += 16
        pts = struct.unpack_from(f"<{2 * nv}f", b, off)
        off += 8 * nv
        xy = list(zip(pts[0::2], pts[1::2]))
        cx, cy = sum(q[0] for q in xy) / nv, sum(q[1] for q in xy) / nv
        h = z1 - ground(cx, cy)
        if h < 2.0 or nv < 3:
            continue
        poly = []
        for x, y in xy:
            lon, lat = from_local(x, y)
            poly.append([lat, lon])
        seed = building_seed(min(q[0] for q in xy), min(q[1] for q in xy), group)
        out.append({"name": f"{('building', 'bridge', 'viaduct', 'bridge tower')[kind] if kind < 4 else kind} {group}",
                    "height_m": h, "polygon": poly, "facade": facade_index(h, seed)})
    s, w = from_local(-half, -half)[1], from_local(-half, -half)[0]
    nn, e = from_local(half, half)[1], from_local(half, half)[0]
    return out, [s, w, nn, e]


def write_terrain_obj(path, terr, x0, y0, sp, n, tex="rock.png", tile=60.0):
    """OBJ8 mesh of the n x n height grid (rows south to north), x east, y up, z south, textured by world metres."""
    out = ["A", "800", "OBJ", f"TEXTURE {tex}", f"POINT_COUNTS {n * n} 0 0 {6 * (n - 1) * (n - 1)}"]
    for j in range(n):
        for i in range(n):
            x, y = x0 + i * sp, y0 + j * sp
            out.append(f"VT {x:.1f} {terr[j][i]:.2f} {-y:.1f} 0 1 0 {x / tile:.3f} {y / tile:.3f}")
    idx = []
    for j in range(n - 1):
        for i in range(n - 1):
            a, b, c, d = j * n + i, j * n + i + 1, (j + 1) * n + i, (j + 1) * n + i + 1
            idx += [a, c, b, b, c, d]       # counter-clockwise seen from above (+y)
    for k in range(0, len(idx), 10):
        chunk = idx[k:k + 10]
        out.append(("IDX10 " if len(chunk) == 10 else "IDX ") + " ".join(map(str, chunk)))
    out.append("ATTR_LOD 0 40000")
    out.append("ATTR_no_cull")           # ponytail: visible from both sides whatever the winding
    out.append(f"TRIS 0 {len(idx)}")
    open(path, "w").write("\n".join(out) + "\n")


def read_grid(dir_):
    """Tools/city-export files -> buildings (as build_dsf takes them, facade by main's rule), terrain grid, bbox."""
    import csv
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from gridmap import to_geo
    blds = []
    for r in list(csv.reader(open(os.path.join(dir_, "buildings.csv"))))[1:]:
        _, lot, x0, y0, x1, y1, z0, z1 = r
        x0, y0, x1, y1, z0, z1 = map(float, (x0, y0, x1, y1, z0, z1))
        poly = [list(to_geo(x, y)) for x, y in ((x0, y0), (x1, y0), (x1, y1), (x0, y1))]
        blds.append({"name": f"box lot {lot}", "height_m": z1, "polygon": poly,
                     "facade": facade_index(z1 - z0, building_seed(x0, y0, int(lot)))})
    terr = [[float(v) for v in r] for r in csv.reader(open(os.path.join(dir_, "terrain.csv")))]
    s, w = to_geo(-3000.0, -3000.0)
    n_, e = to_geo(3000.0, 3000.0)
    return blds, terr, [s, w, n_, e]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--xplane", default=os.path.expanduser("~/X-Plane-12"))
    ap.add_argument("--buildings", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "sf_buildings.json"))
    ap.add_argument("--world", help="build from the bcbf crate's sf_world.bin instead of the JSON")
    ap.add_argument("--grid", metavar="DIR", help="build the gate's procedural city from a Tools/city-export directory")
    args = ap.parse_args()
    terrain_at = None
    if args.grid:
        blds, terr, bbox = read_grid(args.grid)
        data = {"buildings": blds}
        from gridmap import ORIGIN_LAT, ORIGIN_LON
        terrain_at = (ORIGIN_LAT, ORIGIN_LON)
    elif args.world:
        blds, bbox = read_sf_world(args.world)
        data = {"buildings": blds}
    else:
        data = json.load(open(args.buildings))
        bbox = [float(x) for x in data["bbox"].split(",")]
        for i, b in enumerate(data["buildings"]):
            lat0, lon0 = min(p[0] for p in b["polygon"]), min(p[1] for p in b["polygon"])
            b["facade"] = facade_index(b["height_m"], building_seed(lon0 * 1e4, lat0 * 1e4, i))
    root = os.path.join(args.xplane, "Custom Scenery", GRID_PACK if args.grid else PACK)
    os.makedirs(os.path.join(root, "Earth nav data", "+30-130"), exist_ok=True)
    os.makedirs(os.path.join(root, "facades"), exist_ok=True)
    dsf, kept = build_dsf(data["buildings"], bbox, terrain_at)
    if args.grid:
        os.makedirs(os.path.join(root, "objects"), exist_ok=True)
        write_terrain_obj(os.path.join(root, TERRAIN_OBJ), terr, -3000.0, -3000.0, 20.0, len(terr))
        from PIL import Image
        import io
        Image.open(io.BytesIO(texture_bytes("rock"))).convert("RGB").resize((1024, 1024)).save(
            os.path.join(root, "objects", "rock.png"), optimize=True)
    open(os.path.join(root, "Earth nav data", "+30-130", TILE + ".dsf"), "wb").write(dsf)
    for old in ("osm_building.fac", "osm_building.png"):
        if os.path.exists(os.path.join(root, "facades", old)):
            os.remove(os.path.join(root, "facades", old))
    for i in range(len(FACADES) * len(ROOFS)):
        open(os.path.join(root, facade_path(i)), "w").write(fac_text(i // len(ROOFS), i % len(ROOFS)))
    write_textures(os.path.join(root, "facades"))
    counts = [0] * (len(FACADES) * len(ROOFS))
    for b in data["buildings"]:
        counts[b.get("facade", 0)] += 1
    print("facades:", ", ".join(f"{facade_path(i)[8:-4]} {c}" for i, c in enumerate(counts) if c))
    print(f"{kept - bool(terrain_at)} of {len(data['buildings'])} buildings written to {root} ({len(dsf)} byte DSF)")


if __name__ == "__main__":
    main()
