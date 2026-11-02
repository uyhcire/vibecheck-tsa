#!/usr/bin/env python3
"""Build `sf_world.bin` (the San Francisco collision world) from `raw/`.

Needs Python 3 and shapely (`pip install shapely`). The output is committed,
so only regenerating the data needs this.

Every obstacle becomes a vertical prism over a convex polygon (`world.rs`
checks exact segment-to-prism distance). Every step only ever grows an
obstacle, never shrinks it:

  * A footprint whose convex hull overshoots it by more than `TAU` is cut
    into pieces at reflex vertices (along an edge's extension, so an L or U
    splits into its rectangles); each piece becomes its hull. Courtyards are
    filled. The union of the pieces contains the footprint.
  * Hulls are simplified only by dropping an edge and extending its two
    neighbours to meet, which adds a sliver (at most `SIMPLIFY_TOL` thick).
  * Heights: DataSF's maximum LiDAR first return over the footprint (2010),
    not the median. OSM adds buildings the 2010 LiDAR predates and anything
    OSM says is taller; an OSM building is dropped only when DataSF
    footprints at least as tall already cover it.
  * The Bay Bridge West Span is a curtain from the water up to a piecewise-
    linear envelope over its cables (towers 160 m); a straight line between
    two points of a sagging cable lies above it. Elevated freeways are
    curtains from the ground to `VIADUCT_H` above it. Nobody flies under.

Usage: python3 build.py
"""

import json
import math
import os
import re
import struct
import sys
from collections import Counter

import shapely
from shapely.geometry import LineString, MultiPolygon, Point, Polygon, box
from shapely.ops import unary_union
from shapely.strtree import STRtree

from geo import ORIGIN_LAT, ORIGIN_LON, X0, X1, Y0, Y1, gg_corridor, to_local, utm_forward

HERE = os.path.dirname(os.path.abspath(__file__))
RAW = os.path.join(HERE, "raw")
OUT = os.path.join(HERE, "sf_world.bin")

TSP = 20.0
TNX, TNY = round((X1 - X0) / TSP) + 1, round((Y1 - Y0) / TSP) + 1
WATER_LEVEL = 1.0  # ~mean sea level, NAVD88 m; 3DEP flattens the bay to -1.08
TAU = 3.0  # max hull overshoot (m) before a footprint is cut
SIMPLIFY_TOL = 0.25  # max sliver added per simplification step (m)
MIN_AREA = 4.0  # pieces smaller than this are not cut further (m^2)
OSM_LEVEL_H = 3.5  # m per storey when OSM gives only building:levels
OSM_DEFAULT_H = 12.0  # OSM building with no height, no levels, not in DataSF
VIADUCT_H = 24.0  # elevated freeway: curtain up to this far above the ground
BRIDGE_SLICE = 40.0  # bridge curtains are cut into slices this long (m)
MAP = box(X0, Y0, X1, Y1)
# world.rs builds the Golden Gate Bridge itself; OSM and DataSF pieces of it are skipped.
GOLDEN_GATE = Polygon(gg_corridor())

KIND_DATASF, KIND_OSM, KIND_BRIDGE, KIND_VIADUCT = 0, 1, 2, 3


# ---------------------------------------------------------------- terrain


def load_terrain():
    raw = open(os.path.join(RAW, "dem_20m.f32"), "rb").read()
    dem = struct.unpack(f"<{TNX * TNY}f", raw)
    # exportImage rows run north to south; the world grid runs south to north.
    t = [0.0] * (TNX * TNY)
    for j in range(TNY):
        for i in range(TNX):
            t[j * TNX + i] = max(dem[(TNY - 1 - j) * TNX + i], WATER_LEVEL)
    return t


def terrain_at(t, x, y):
    """Barycentric height on the render triangulation (same as world.rs)."""
    fx = min(max((x - X0) / TSP, 0.0), TNX - 1 - 1e-9)
    fy = min(max((y - Y0) / TSP, 0.0), TNY - 1 - 1e-9)
    i, j = int(fx), int(fy)
    u, v = fx - i, fy - j
    h00, h10 = t[j * TNX + i], t[j * TNX + i + 1]
    h01, h11 = t[(j + 1) * TNX + i], t[(j + 1) * TNX + i + 1]
    if u >= v:
        return h00 + u * (h10 - h00) + v * (h11 - h10)
    return h00 + v * (h01 - h00) + u * (h11 - h01)


def terrain_range(t, poly):
    """Min and max terrain over a polygon: its vertices and the grid nodes
    inside (the surface is linear on each triangle, so that is close; the
    Rust loader lowers prism bases again against its own terrain)."""
    pts = list(poly.exterior.coords)
    x0, y0, x1, y1 = poly.bounds
    i0, i1 = math.ceil((x0 - X0) / TSP), math.floor((x1 - X0) / TSP)
    j0, j1 = math.ceil((y0 - Y0) / TSP), math.floor((y1 - Y0) / TSP)
    for j in range(max(j0, 0), min(j1, TNY - 1) + 1):
        for i in range(max(i0, 0), min(i1, TNX - 1) + 1):
            x, y = X0 + i * TSP, Y0 + j * TSP
            if poly.contains(Point(x, y)):
                pts.append((x, y))
    hs = [terrain_at(t, x, y) for x, y in pts]
    return min(hs), max(hs)


# ---------------------------------------------------------------- geometry


def polygons_of(g):
    if g.is_empty:
        return []
    if isinstance(g, Polygon):
        return [g]
    if isinstance(g, MultiPolygon):
        return list(g.geoms)
    return [p for p in getattr(g, "geoms", []) if isinstance(p, Polygon)]


def clean(ring):
    """Valid hole-free polygons from a ring (self-intersections resolved)."""
    if len(ring) < 4:
        return []
    p = Polygon(ring)
    if not p.is_valid:
        p = p.buffer(0)
    return [Polygon(q.exterior) for q in polygons_of(p) if q.area > 0.05]


def overshoot(p):
    """How far the convex hull reaches beyond the polygon (m)."""
    h = p.convex_hull
    if h.area - p.area < 1e-6:
        return 0.0
    return shapely.hausdorff_distance(h, p, densify=0.05)


def reflex_vertices(p):
    c = list(p.exterior.coords)[:-1]
    if Polygon(c).exterior.is_ccw is False:
        c = c[::-1]
    n = len(c)
    out = []
    for k in range(n):
        a, b, d = c[k - 1], c[k], c[(k + 1) % n]
        cross = (b[0] - a[0]) * (d[1] - b[1]) - (b[1] - a[1]) * (d[0] - b[0])
        if cross < -1e-9:
            out.append((a, b, d))
    return out


def half_planes(pt, direction, r=2000.0):
    (px, py), (dx, dy) = pt, direction
    ln = math.hypot(dx, dy)
    dx, dy = dx / ln, dy / ln
    nx, ny = -dy, dx
    a = (px - dx * r, py - dy * r)
    b = (px + dx * r, py + dy * r)
    left = Polygon([a, b, (b[0] + nx * r, b[1] + ny * r), (a[0] + nx * r, a[1] + ny * r)])
    right = Polygon([a, b, (b[0] - nx * r, b[1] - ny * r), (a[0] - nx * r, a[1] - ny * r)])
    return left, right


def split_by(p, pt, direction):
    left, right = half_planes(pt, direction)
    parts = []
    for side in (left, right):
        parts += [q for q in polygons_of(p.intersection(side)) if q.area > 1e-4]
    return parts


def decompose(p, depth=0):
    """Convex pieces whose union contains `p`, each overshooting its part of
    `p` by at most TAU (or as close as 8 levels of cuts get)."""
    if depth >= 8 or p.area < MIN_AREA or overshoot(p) <= TAU:
        return [p.convex_hull]
    hull = p.convex_hull
    rv = reflex_vertices(p)
    rv.sort(key=lambda v: -hull.exterior.distance(Point(v[1])))
    best = None
    for a, b, d in rv[:4]:
        for direction in ((b[0] - a[0], b[1] - a[1]), (d[0] - b[0], d[1] - b[1])):
            if math.hypot(*direction) < 1e-6:
                continue
            parts = split_by(p, b, direction)
            if len(parts) < 2:
                continue
            excess = sum(q.convex_hull.area - q.area for q in parts)
            if best is None or excess < best[0]:
                best = (excess, parts)
    if best is None:
        return [hull]
    out = []
    for q in best[1]:
        out += decompose(q, depth + 1)
    return out


def ccw_vertices(hull):
    if not isinstance(hull, Polygon) or hull.area < 1e-3:
        return None
    c = list(hull.exterior.coords)[:-1]
    if not hull.exterior.is_ccw:
        c = c[::-1]
    return c


def simplify_convex(c):
    """Drop edges of a convex CCW polygon by extending their neighbours to
    meet, while the added triangle is thinner than SIMPLIFY_TOL. The result
    contains the input."""

    def meet(p0, p1, q0, q1):
        # intersection of lines p0p1 and q0q1
        d1 = (p1[0] - p0[0], p1[1] - p0[1])
        d2 = (q1[0] - q0[0], q1[1] - q0[1])
        den = d1[0] * d2[1] - d1[1] * d2[0]
        if abs(den) < 1e-12:
            return None
        s = ((q0[0] - p0[0]) * d2[1] - (q0[1] - p0[1]) * d2[0]) / den
        return (p0[0] + s * d1[0], p0[1] + s * d1[1]), s

    changed = True
    while changed and len(c) > 3:
        changed = False
        n = len(c)
        best = None
        for k in range(n):
            # edge c[k] -> c[k+1], neighbours c[k-1]->c[k] and c[k+1]->c[k+2]
            a, b, d, e = c[k - 1], c[k], c[(k + 1) % n], c[(k + 2) % n]
            m = meet(a, b, d, e)
            if m is None:
                continue
            x, s = m
            if s <= 1.0:  # neighbours diverge: extending them never closes
                continue
            ex, ey = d[0] - b[0], d[1] - b[1]
            ln = math.hypot(ex, ey)
            if ln < 1e-9:
                continue
            h = abs((x[0] - b[0]) * ey - (x[1] - b[1]) * ex) / ln
            if h <= SIMPLIFY_TOL and (best is None or h < best[0]):
                best = (h, k, x)
        if best is not None:
            _, k, x = best
            n = len(c)
            c = [x if i == k else c[i] for i in range(n) if i != (k + 1) % n]
            changed = True
    return c


# ---------------------------------------------------------------- sources


def parse_height(s):
    if s is None:
        return None
    s = s.strip().lower().replace(",", ".")
    m = re.match(r"^([0-9.]+)\s*(m|meters|metres)?$", s)
    if m:
        return float(m.group(1))
    m = re.match(r"^([0-9.]+)\s*(ft|feet|')$", s)
    if m:
        return float(m.group(1)) * 0.3048
    m = re.match(r"^(\d+)'\s*(\d+)\"?$", s)
    if m:
        return int(m.group(1)) * 0.3048 + int(m.group(2)) * 0.0254
    return None


def in_map(p):
    return p.intersects(MAP) and not GOLDEN_GATE.contains(p.centroid)


def datasf_buildings():
    d = json.load(open(os.path.join(RAW, "datasf_footprints.geojson")))
    out = []
    for f in d["features"]:
        g, pr = f["geometry"], f["properties"]
        if g is None or pr.get("maxcm_1st") is None or pr.get("gnd_mincm") is None:
            continue
        top, gnd = float(pr["maxcm_1st"]) / 100, float(pr["gnd_mincm"]) / 100
        rings = g["coordinates"] if g["type"] == "MultiPolygon" else [g["coordinates"]]
        for r in rings:
            for p in clean([to_local(lon, lat) for lon, lat in r[0]]):
                if in_map(p):
                    out.append((p, gnd, max(top, gnd + 2.0), pr["sf16_bldgid"]))
    out.sort(key=lambda b: b[3])
    return out


def osm_rings(e):
    if e["type"] == "way":
        g = e.get("geometry")
        return [[to_local(q["lon"], q["lat"]) for q in g]] if g else []
    rings = []
    for m in e.get("members", []):
        if m.get("role") == "outer" and m.get("geometry"):
            rings.append([to_local(q["lon"], q["lat"]) for q in m["geometry"]])
    return rings


def underground(t):
    if t.get("location") in ("underground", "underwater"):
        return True
    try:
        return int(t.get("layer", "0")) < 0 and "height" not in t
    except ValueError:
        return False


def osm_buildings():
    d = json.load(open(os.path.join(RAW, "osm_buildings.json")))
    out = []
    for e in sorted(d["elements"], key=lambda e: (e["type"], e["id"])):
        t = e.get("tags", {})
        if underground(t):
            continue
        h = parse_height(t.get("height"))
        if h is None and t.get("building:levels"):
            try:
                h = float(t["building:levels"]) * OSM_LEVEL_H + 1.0
            except ValueError:
                pass
        name = t.get("name", "")
        for r in osm_rings(e):
            for p in clean(r):
                if in_map(p):
                    out.append((p, h, f"osm/{e['type']}/{e['id']}", name))
    return out


# ---------------------------------------------------------------- bridge


def bay_bridge(terr):
    """West Span curtain slices: (polygon, z0, z1)."""
    d = json.load(open(os.path.join(RAW, "osm_bridges.json")))
    outline, piers = None, {}
    for e in d["elements"]:
        t = e.get("tags", {})
        if e["type"] == "way" and t.get("man_made") == "bridge" and "West Span" in t.get("name", ""):
            outline = clean([to_local(q["lon"], q["lat"]) for q in e["geometry"]])[0]
        if e["type"] == "way" and t.get("ref", "").startswith("W") and "bridge:support" in t:
            pts = [to_local(q["lon"], q["lat"]) for q in e["geometry"]]
            piers[t["ref"]] = Polygon(pts).centroid if len(pts) > 3 else LineString(pts).centroid
    if outline is None or not {"W1", "W2", "W3", "W5", "W6", "W7"} <= piers.keys():
        raise SystemExit("Bay Bridge West Span outline or piers missing from osm_bridges.json")
    # Axis W1 -> W7; stations along it.
    a, b = piers["W1"], piers["W7"]
    ux, uy = b.x - a.x, b.y - a.y
    ln = math.hypot(ux, uy)
    ux, uy = ux / ln, uy / ln

    def station(p):
        return (p.x - a.x) * ux + (p.y - a.y) * uy

    s = {k: station(v) for k, v in piers.items()}
    # Cable envelope (m above datum): towers 160 m; main spans sag to 100 m;
    # cables anchor at about 80 m on the centre anchorage (W4, 67 m tall)
    # and come down to 60-70 m at the shore anchorages.
    env = sorted(
        [
            (s["W1"] - 400.0, 60.0),
            (s["W1"], 60.0),
            (s["W2"], 160.0),
            (0.5 * (s["W2"] + s["W3"]), 100.0),
            (s["W3"], 160.0),
            (s["W4"], 80.0),
            (s["W5"], 160.0),
            (0.5 * (s["W5"] + s["W6"]), 100.0),
            (s["W6"], 160.0),
            (s["W7"], 70.0),
            (s["W7"] + 400.0, 70.0),
        ]
    )

    def env_max(s0, s1):
        def at(q):
            for (p0, h0), (p1, h1) in zip(env, env[1:]):
                if p0 <= q <= p1:
                    return h0 + (h1 - h0) * (q - p0) / (p1 - p0)
            return env[0][1] if q < env[0][0] else env[-1][1]

        return max([at(s0), at(s1)] + [h for p, h in env if s0 <= p <= s1])

    out = []
    smin = min(station(Point(q)) for q in outline.exterior.coords)
    smax = max(station(Point(q)) for q in outline.exterior.coords)
    k = math.floor(smin / BRIDGE_SLICE)
    while k * BRIDGE_SLICE < smax:
        s0, s1 = k * BRIDGE_SLICE, (k + 1) * BRIDGE_SLICE
        # strip between stations s0 and s1
        nx, ny = -uy, ux
        r = 500.0
        strip = Polygon(
            [
                (a.x + ux * s0 - nx * r, a.y + uy * s0 - ny * r),
                (a.x + ux * s1 - nx * r, a.y + uy * s1 - ny * r),
                (a.x + ux * s1 + nx * r, a.y + uy * s1 + ny * r),
                (a.x + ux * s0 + nx * r, a.y + uy * s0 + ny * r),
            ]
        )
        for p in polygons_of(outline.intersection(strip)):
            if in_map(p) and p.area > 0.5:
                zlo, _ = terrain_range(terr, p)
                out.append((p, min(zlo, WATER_LEVEL) - 3.0, env_max(s0, s1)))
        k += 1
    return out


def viaducts(terr, bridge_outline_union):
    d = json.load(open(os.path.join(RAW, "osm_streets.json")))
    out = []
    for e in sorted(d["elements"], key=lambda e: e["id"]):
        t = e.get("tags", {})
        if t.get("bridge") not in ("yes", "viaduct") or not t.get("highway", "").startswith(("motorway", "trunk")):
            continue
        pts = [to_local(q["lon"], q["lat"]) for q in e["geometry"]]
        try:
            lanes = int(t.get("lanes", "1" if "_link" in t["highway"] else "3"))
        except ValueError:
            lanes = 3
        width = lanes * 3.7 + 4.0
        for q0, q1 in zip(pts, pts[1:]):
            seg = LineString([q0, q1])
            n = max(1, math.ceil(seg.length / BRIDGE_SLICE))
            for k in range(n):
                sub = LineString([seg.interpolate(k / n, normalized=True), seg.interpolate((k + 1) / n, normalized=True)])
                p = sub.buffer(width / 2, cap_style="flat")
                if not in_map(p) or p.area < 1.0 or bridge_outline_union.contains(p) or GOLDEN_GATE.intersects(p):
                    continue
                zlo, zhi = terrain_range(terr, p)
                out.append((p, zlo, zhi + VIADUCT_H))
    return out


# ---------------------------------------------------------------- streets

STREET_CLASSES = [
    "motorway",
    "trunk",
    "primary",
    "secondary",
    "tertiary",
    "unclassified",
    "residential",
    "motorway_link",
    "trunk_link",
    "primary_link",
    "secondary_link",
]


def streets():
    d = json.load(open(os.path.join(RAW, "osm_streets.json")))
    out = []
    for e in sorted(d["elements"], key=lambda e: e["id"]):
        t = e.get("tags", {})
        hw = t.get("highway")
        if hw not in STREET_CLASSES or "geometry" not in e:
            continue
        if t.get("tunnel") in ("yes", "building_passage") or t.get("layer", "0").startswith("-"):
            continue
        pts = [to_local(q["lon"], q["lat"]) for q in e["geometry"]]
        if not LineString(pts).intersects(MAP):
            continue
        flags = 1 if t.get("bridge") else 0
        out.append((STREET_CLASSES.index(hw), flags, t.get("name", ""), pts))
    return out


# ---------------------------------------------------------------- main


def main():
    terr = load_terrain()
    stats = Counter()

    ds = datasf_buildings()
    stats["datasf polygons"] = len(ds)
    ds_tree = STRtree([b[0] for b in ds])

    pieces = []  # (vertices, z0, z1, kind, group)
    group = 0

    def emit(poly, z0, z1, kind):
        nonlocal group
        for part in decompose(poly):
            c = ccw_vertices(part)
            if c is None:
                continue
            c = simplify_convex(c)
            pieces.append((c, z0, z1, kind, group))
            stats[f"pieces kind {kind}"] += 1
        group += 1

    for p, gnd, top, _ in ds:
        emit(p, gnd, top, KIND_DATASF)

    # OSM: keep what DataSF does not already cover at least as tall.
    for p, h, oid, name in osm_buildings():
        idx = ds_tree.query(p)
        cover = [ds[i] for i in idx if ds[i][0].intersects(p)]
        covered_area = sum(c[0].intersection(p).area for c in cover)
        gmin, _ = terrain_range(terr, p)
        if h is None:
            if covered_area >= 0.5 * p.area:
                stats["osm skipped: no height, in DataSF"] += 1
                continue
            h = OSM_DEFAULT_H
            stats["osm default height"] += 1
        top = gmin + h
        tall = [c[0] for c in cover if c[2] >= top - 1.0]
        core = p.buffer(-1.5)
        if tall and (core.is_empty or core.difference(unary_union(tall)).area < 1.0):
            stats["osm skipped: DataSF as tall"] += 1
            continue
        stats["osm added"] += 1
        if h > 120:
            print(f"  OSM tall: {name or oid} {h:.0f} m", file=sys.stderr)
        emit(p, gmin, top, KIND_OSM)

    br = bay_bridge(terr)
    for p, z0, z1 in br:
        emit(p, z0, z1, KIND_BRIDGE)
    bunion = unary_union([b[0] for b in br]).buffer(2.0)
    for p, z0, z1 in viaducts(terr, bunion):
        emit(p, z0, z1, KIND_VIADUCT)

    st = streets()
    names = sorted({s[2] for s in st})
    name_idx = {n: k for k, n in enumerate(names)}

    nv = [len(c) for c, *_ in pieces]
    nv.sort()
    for k, v in sorted(stats.items()):
        print(f"{k:>40}: {v}", file=sys.stderr)
    print(
        f"{'pieces':>40}: {len(pieces)}; vertices p50 {nv[len(nv) // 2]}, p99 {nv[int(len(nv) * 0.99)]}, max {nv[-1]}",
        file=sys.stderr,
    )
    print(f"{'streets':>40}: {len(st)} ways, {len(names)} names", file=sys.stderr)

    e0, n0 = utm_forward(ORIGIN_LON, ORIGIN_LAT)
    b = bytearray()
    b += b"SFW1"
    b += struct.pack("<I", 2)
    b += struct.pack("<4d", ORIGIN_LON, ORIGIN_LAT, e0, n0)
    b += struct.pack("<4d", X0, Y0, X1, Y1)
    b += struct.pack("<IIf", TNX, TNY, TSP)
    b += struct.pack(f"<{TNX * TNY}f", *terr)
    b += struct.pack("<I", len(pieces))
    for c, z0, z1, kind, grp in pieces:
        b += struct.pack("<ffBBHI", z0, z1, kind, len(c), 0, grp)
        b += struct.pack(f"<{2 * len(c)}f", *[v for q in c for v in q])
    b += struct.pack("<I", len(names))
    for n in names:
        u = n.encode("utf-8")
        b += struct.pack("<H", len(u)) + u
    b += struct.pack("<I", len(st))
    for cls, flags, name, pts in st:
        b += struct.pack("<BBHI", cls, flags, name_idx[name], len(pts))
        b += struct.pack(f"<{2 * len(pts)}f", *[v for q in pts for v in q])
    with open(OUT, "wb") as f:
        f.write(b)
    print(f"wrote {OUT}: {len(b) / 1e6:.2f} MB", file=sys.stderr)


if __name__ == "__main__":
    main()
