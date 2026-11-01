#!/usr/bin/env python3
"""Download the raw San Francisco data the collision world is built from.

Python standard library only. Writes into `raw/` next to this file (not
committed); `build.py` turns it into `sf_world.bin` (committed), so the demo
and the harness never need the network.

Sources:
  * DataSF Building Footprints (ynuv-fyni): footprint polygons with LiDAR
    height statistics (2010 Pictometry LiDAR, footprints refined 2016).
  * OpenStreetMap via Overpass: buildings and building parts with heights
    (newer towers the 2010 LiDAR predates), streets, and the Bay Bridge.
  * USGS 3DEP bare-earth elevation (ImageServer exportImage), NAVD88 metres.

Usage: python3 fetch.py [--force]
"""

import json
import os
import sys
import time
import urllib.parse
import urllib.request

from geo import ORIGIN_LON, ORIGIN_LAT, HALF, FETCH_MARGIN, utm_forward, lonlat_bbox

HERE = os.path.dirname(os.path.abspath(__file__))
RAW = os.path.join(HERE, "raw")
UA = "cityflight-data/0.1 (backup-CBF flight demo)"
OVERPASS = "https://overpass-api.de/api/interpreter"


def get(url, data=None, timeout=300, tries=4):
    for k in range(tries):
        try:
            req = urllib.request.Request(url, data=data, headers={"User-Agent": UA})
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.read()
        except Exception as e:  # noqa: BLE001 - network: retry anything
            if k == tries - 1:
                raise
            wait = 10 * (k + 1)
            print(f"  retry in {wait}s after: {e}", file=sys.stderr)
            time.sleep(wait)


def cached(name, force):
    path = os.path.join(RAW, name)
    return path, (os.path.exists(path) and not force)


def fetch_datasf(force):
    path, ok = cached("datasf_footprints.geojson", force)
    if ok:
        return
    w, s, e, n = lonlat_bbox(HALF + FETCH_MARGIN)
    poly = f"POLYGON(({w} {s}, {e} {s}, {e} {n}, {w} {n}, {w} {s}))"
    fields = "sf16_bldgid,maxcm_1st,gnd_mincm,hgt_maxcm,hgt_mediancm,shape"
    feats, offset, page = [], 0, 20000
    while True:
        q = urllib.parse.urlencode(
            {
                "$select": fields,
                "$where": f"intersects(shape, '{poly}')",
                "$order": "sf16_bldgid",
                "$limit": page,
                "$offset": offset,
            }
        )
        print(f"DataSF footprints, offset {offset}...", file=sys.stderr)
        d = json.loads(get("https://data.sf.gov/resource/ynuv-fyni.geojson?" + q))
        feats += d["features"]
        if len(d["features"]) < page:
            break
        offset += page
    with open(path, "w") as f:
        json.dump({"type": "FeatureCollection", "features": feats}, f)
    print(f"  {len(feats)} footprints", file=sys.stderr)


def overpass(query):
    return json.loads(get(OVERPASS, data=urllib.parse.urlencode({"data": query}).encode(), timeout=400))


def fetch_osm(force):
    w, s, e, n = lonlat_bbox(HALF + FETCH_MARGIN)
    bb = f"{s},{w},{n},{e}"
    jobs = [
        (
            "osm_buildings.json",
            f'[out:json][timeout:300];(way["building"]({bb});way["building:part"]({bb});'
            f'relation["building"]({bb});relation["building:part"]({bb}););out geom tags;',
        ),
        (
            "osm_streets.json",
            f'[out:json][timeout:300];way["highway"~"^(motorway|trunk|primary|secondary|tertiary|'
            f'unclassified|residential|motorway_link|trunk_link|primary_link|secondary_link)$"]({bb});'
            f"out geom tags;",
        ),
        (
            "osm_bridges.json",
            f'[out:json][timeout:300];(way["man_made"="bridge"]({bb});way["bridge"]["highway"]({bb});'
            f'node["bridge:support"]({bb});way["bridge:support"]({bb});'
            f'node["man_made"~"^(tower|mast|crane)$"]({bb});way["man_made"~"^(tower|mast)$"]({bb}););'
            f"out geom tags;",
        ),
    ]
    for name, query in jobs:
        path, ok = cached(name, force)
        if ok:
            continue
        print(f"Overpass: {name}...", file=sys.stderr)
        d = overpass(query)
        with open(path, "w") as f:
            json.dump(d, f)
        print(f"  {len(d['elements'])} elements", file=sys.stderr)


def fetch_dem(force):
    """Bare-earth heights at the 20 m terrain nodes, in UTM 10N metres.

    exportImage takes the outer edges of the pixel grid, so a node grid
    x_i = -HALF + 20 i (i = 0..300) is 301 pixels whose edges are half a
    pixel outside the nodes.
    """
    path, ok = cached("dem_20m.f32", force)
    if ok:
        return
    tsp, tn = 20.0, 301
    e0, n0 = utm_forward(ORIGIN_LON, ORIGIN_LAT)
    xmin, ymin = e0 - HALF - tsp / 2, n0 - HALF - tsp / 2
    xmax, ymax = e0 + HALF + tsp / 2, n0 + HALF + tsp / 2
    q = urllib.parse.urlencode(
        {
            "bbox": f"{xmin},{ymin},{xmax},{ymax}",
            "bboxSR": 32610,
            "imageSR": 32610,
            "size": f"{tn},{tn}",
            "format": "bsq",
            "pixelType": "F32",
            "interpolation": "RSP_BilinearInterpolation",
            "f": "image",
        }
    )
    print("USGS 3DEP DEM...", file=sys.stderr)
    data = get("https://elevation.nationalmap.gov/arcgis/rest/services/3DEPElevation/ImageServer/exportImage?" + q)
    need = tn * tn * 4
    if len(data) < need:
        raise SystemExit(f"DEM: expected {need} bytes, got {len(data)}: {data[:200]!r}")
    with open(path, "wb") as f:
        f.write(data[:need])


def main():
    force = "--force" in sys.argv
    os.makedirs(RAW, exist_ok=True)
    fetch_dem(force)
    fetch_datasf(force)
    fetch_osm(force)
    print("done; now run build.py", file=sys.stderr)


if __name__ == "__main__":
    main()
