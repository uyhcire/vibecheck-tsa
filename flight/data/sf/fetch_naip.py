#!/usr/bin/env python3
"""Download USDA NAIP aerial imagery (public domain) for the San Francisco
map and stitch it into `sf_naip.jpg` (8192 x 8192, ~0.73 m per pixel, row 0
= north edge). Needs Pillow for the stitching (`pip install pillow`).

The USGS NAIP ImageServer reprojects into the map frame (UTM 10N) itself,
so each pixel lines up with world.rs coordinates:
x = -HALF + (col + 0.5) * 2 * HALF / 8192, likewise y from the bottom row.
"""

import io
import os
import sys
import urllib.parse

from PIL import Image

from fetch import get
from geo import HALF, ORIGIN_LAT, ORIGIN_LON, utm_forward

HERE = os.path.dirname(os.path.abspath(__file__))
N = 8192
TILES = 4  # 4 x 4 requests of 2048 px (the server allows 4000 per side)
OUT = os.path.join(HERE, "sf_naip.jpg")


def fetch_tile(tj, ti):
    """One tile (tj from the north edge), cached in raw/."""
    path = os.path.join(HERE, "raw", f"naip_{TILES}_{tj}_{ti}.jpg")
    if os.path.exists(path):
        return path
    e0, n0 = utm_forward(ORIGIN_LON, ORIGIN_LAT)
    step = 2 * HALF / TILES
    x0 = e0 - HALF + ti * step
    y1 = n0 + HALF - tj * step
    q = urllib.parse.urlencode(
        {
            "bbox": f"{x0},{y1 - step},{x0 + step},{y1}",
            "bboxSR": 32610,
            "imageSR": 32610,
            "size": f"{N // TILES},{N // TILES}",
            "format": "jpg",
            "compressionQuality": 92,
            "f": "image",
        }
    )
    data = get("https://imagery.nationalmap.gov/arcgis/rest/services/USGSNAIPImagery/ImageServer/exportImage?" + q, tries=8)
    Image.open(io.BytesIO(data)).verify()
    with open(path + ".part", "wb") as f:
        f.write(data)
    os.replace(path + ".part", path)
    print(f"  tile {tj},{ti}", file=sys.stderr)
    return path


def main():
    from concurrent.futures import ThreadPoolExecutor

    os.makedirs(os.path.join(HERE, "raw"), exist_ok=True)
    jobs = [(tj, ti) for tj in range(TILES) for ti in range(TILES)]
    with ThreadPoolExecutor(4) as ex:
        paths = list(ex.map(lambda t: fetch_tile(*t), jobs))
    px = N // TILES
    img = Image.new("RGB", (N, N))
    for (tj, ti), path in zip(jobs, paths):
        tile = Image.open(path).convert("RGB")
        assert tile.size == (px, px), tile.size
        img.paste(tile, (ti * px, tj * px))
    img.save(OUT, quality=85, optimize=True)
    print(f"wrote {OUT}: {os.path.getsize(OUT) / 1e6:.1f} MB", file=sys.stderr)


if __name__ == "__main__":
    main()
