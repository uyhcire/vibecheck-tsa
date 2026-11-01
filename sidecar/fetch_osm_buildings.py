"""Fetch building footprints with heights from OpenStreetMap (Overpass) into a JSON obstacle set.

usage: python3 -I sidecar/fetch_osm_buildings.py [--bbox S,W,N,E] [--min-height M] [--out sidecar/sf_buildings.json]
Default box covers downtown San Francisco (Financial District, SoMa, Embarcadero).
"""
import argparse
import json
import urllib.parse
import urllib.request

OVERPASS = "https://overpass-api.de/api/interpreter"


def height_m(tags):
    h = tags.get("height") or tags.get("building:height")
    if h:
        try:
            return float(h.replace("m", "").strip().split()[0])
        except ValueError:
            pass
    lv = tags.get("building:levels")
    if lv:
        try:
            return float(lv) * 3.5
        except ValueError:
            pass
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bbox", default="37.780,-122.412,37.805,-122.385", help="south,west,north,east")
    ap.add_argument("--min-height", type=float, default=20.0, help="drop buildings lower than this (m)")
    ap.add_argument("--out", default="sidecar/sf_buildings.json")
    args = ap.parse_args()
    q = f'[out:json][timeout:120];(way["building"]({args.bbox});relation["building"]({args.bbox}););out body geom;'
    req = urllib.request.Request(OVERPASS, data=urllib.parse.urlencode({"data": q}).encode(),
                                 headers={"User-Agent": "vibecheck-tsa sidecar"})
    with urllib.request.urlopen(req, timeout=180) as r:
        data = json.load(r)
    out, skipped = [], 0
    for el in data["elements"]:
        tags = el.get("tags", {})
        h = height_m(tags)
        if h is None or h < args.min_height:
            skipped += 1
            continue
        if el["type"] == "way":
            rings = [el.get("geometry", [])]
        else:  # relation: outer rings only
            rings = [m.get("geometry", []) for m in el.get("members", []) if m.get("role") == "outer"]
        for g in rings:
            poly = [[round(p["lat"], 6), round(p["lon"], 6)] for p in g]
            if len(poly) >= 4:
                out.append({"name": tags.get("name") or f'{el["type"]}/{el["id"]}', "height_m": round(h, 1), "polygon": poly})
    out.sort(key=lambda b: -b["height_m"])
    json.dump({"bbox": args.bbox, "min_height_m": args.min_height, "source": "OpenStreetMap via Overpass", "buildings": out},
              open(args.out, "w"), indent=0)
    print(f"{len(out)} buildings >= {args.min_height} m written to {args.out} ({skipped} without usable height or too low)")
    for b in out[:8]:
        print(f"  {b['height_m']:6.1f} m  {b['name']}")


if __name__ == "__main__":
    main()
