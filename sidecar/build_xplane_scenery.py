"""Build an X-Plane custom scenery pack that draws exactly the obstacle set.

Every polygon in sf_buildings.json becomes a facade extruded to its height, and X-Plane's own
buildings, autogen and forests are excluded inside the obstacle box, so what X-Plane renders
there is the JSON and nothing else. Writes the DSF tile directly (no DSFTool needed).

usage: python3 -I sidecar/build_xplane_scenery.py [--xplane ~/X-Plane-12] [--buildings sidecar/sf_buildings.json]
"""
import argparse
import hashlib
import json
import os
import struct
import zlib

PACK = "OSM Obstacles - SF Downtown"
TILE = "+37-123"
FACADE = "facades/osm_building.fac"


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


def build_dsf(buildings, bbox):
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
    defn = atom("DEFN", atom("TERT", b"") + atom("OBJT", b"") + atom("POLY", strings([FACADE]))
                + atom("NETW", b"") + atom("DEMN", b""))
    pools, scals, cmds = b"", b"", b""
    cmds += struct.pack("<BB", 3, 0)                        # SET_DEFINITION8: facade 0
    kept = 0
    for i, b in enumerate(buildings):
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


def png_rgba(w, h, pixel):
    raw = b"".join(b"\0" + b"".join(bytes(pixel(x, y)) for x in range(w)) for y in range(h))
    def chunk(t, d):
        return struct.pack(">I", len(d)) + t + d + struct.pack(">I", zlib.crc32(t + d) & 0xFFFFFFFF)
    return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 6, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(raw, 9)) + chunk(b"IEND", b""))


def wall_pixel(x, y):
    if x >= 192:                                   # roof strip: flat grey
        return (92, 92, 96, 255)
    bay, floor = x % 32, y % 32
    window = 6 <= bay <= 25 and 8 <= floor <= 24
    return (70, 110, 150, 255) if window else (150, 148, 142, 255)


FAC = """A
800
FACADE

TEXTURE osm_building.png
RING 1
TWO_SIDED 1
LOD 0.000000 30000.000000
  ROOF 0.750000 0.000000
  ROOF 1.000000 0.000000
  ROOF 1.000000 0.250000
  ROOF 0.750000 0.250000
  WALL 0.000000 100000.000000
    SCALE 24.000000 24.000000
    ROOF_SLOPE 0.000000
    LEFT 0.000000 0.125000
    CENTER 0.125000 0.250000
    CENTER 0.250000 0.375000
    CENTER 0.375000 0.500000
    RIGHT 0.500000 0.625000
    BOTTOM 0.000000 0.125000
    MIDDLE 0.125000 0.250000
    MIDDLE 0.250000 0.375000
    TOP 0.375000 0.500000
"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--xplane", default=os.path.expanduser("~/X-Plane-12"))
    ap.add_argument("--buildings", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "sf_buildings.json"))
    args = ap.parse_args()
    data = json.load(open(args.buildings))
    bbox = [float(x) for x in data["bbox"].split(",")]
    root = os.path.join(args.xplane, "Custom Scenery", PACK)
    os.makedirs(os.path.join(root, "Earth nav data", "+30-130"), exist_ok=True)
    os.makedirs(os.path.join(root, "facades"), exist_ok=True)
    dsf, kept = build_dsf(data["buildings"], bbox)
    open(os.path.join(root, "Earth nav data", "+30-130", TILE + ".dsf"), "wb").write(dsf)
    open(os.path.join(root, FACADE), "w").write(FAC)
    open(os.path.join(root, "facades", "osm_building.png"), "wb").write(png_rgba(256, 256, wall_pixel))
    print(f"{kept} of {len(data['buildings'])} buildings written to {root} ({len(dsf)} byte DSF)")


if __name__ == "__main__":
    main()
