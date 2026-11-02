#!/usr/bin/env python3
"""Download USDA NAIP aerial imagery (public domain) for the San Francisco
map and stitch it into `sf_naip.jpg` (1 m per pixel over the flyable
rectangle, 12600 x 9400, row 0 = north edge). Needs Pillow for the stitching
(`pip install pillow`).

The USGS NAIP ImageServer reprojects into the map frame (UTM 10N) itself,
so each pixel lines up with world.rs coordinates:
x = X0 + (col + 0.5) m, y = Y1 - (row + 0.5) m.
"""

import io
import os
import sys
import urllib.parse

from PIL import Image

from fetch import get
from geo import ORIGIN_LAT, ORIGIN_LON, X0, X1, Y0, Y1, utm_forward

HERE = os.path.dirname(os.path.abspath(__file__))
PX = 1.0  # metres per pixel
NX, NY = round((X1 - X0) / PX), round((Y1 - Y0) / PX)
TX, TY = 6, 4  # tiles across and down (the server allows 4000 px per side)
OUT = os.path.join(HERE, "sf_naip.jpg")


def fetch_tile(tj, ti):
    """One tile (tj from the north edge), cached in raw/."""
    path = os.path.join(HERE, "raw", f"naip_{NX}x{NY}_{tj}_{ti}.jpg")
    if os.path.exists(path):
        return path
    e0, n0 = utm_forward(ORIGIN_LON, ORIGIN_LAT)
    sx, sy = (X1 - X0) / TX, (Y1 - Y0) / TY
    x0 = e0 + X0 + ti * sx
    y1 = n0 + Y1 - tj * sy
    q = urllib.parse.urlencode(
        {
            "bbox": f"{x0},{y1 - sy},{x0 + sx},{y1}",
            "bboxSR": 32610,
            "imageSR": 32610,
            "size": f"{NX // TX},{NY // TY}",
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
    assert NX % TX == 0 and NY % TY == 0
    jobs = [(tj, ti) for tj in range(TY) for ti in range(TX)]
    with ThreadPoolExecutor(4) as ex:
        paths = list(ex.map(lambda t: fetch_tile(*t), jobs))
    px, py = NX // TX, NY // TY
    img = Image.new("RGB", (NX, NY))
    for (tj, ti), path in zip(jobs, paths):
        tile = Image.open(path).convert("RGB")
        assert tile.size == (px, py), tile.size
        img.paste(tile, (ti * px, tj * py))
    img.save(OUT, quality=85, optimize=True)
    print(f"wrote {OUT}: {os.path.getsize(OUT) / 1e6:.1f} MB", file=sys.stderr)


if __name__ == "__main__":
    main()
