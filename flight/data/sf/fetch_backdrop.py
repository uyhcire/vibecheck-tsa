#!/usr/bin/env python3
"""Download the Bay Area backdrop, drawn beyond the flyable 6 km square
(visual only; the square's edge is a wall to the safety filter). Needs
Pillow (`pip install pillow`).

  backdrop_dem.f32  terrain, USGS 3DEP: 801 x 801 nodes at 100 m over an
                    80 km square, little-endian float32, row 0 = south
  backdrop.jpg      aerial imagery, USDA NAIP: 4096 x 4096 (19.5 m per
                    pixel) over the same square, row 0 = north

Both are in the map frame (UTM 10N around the origin in geo.py), so they
line up with world.rs coordinates.
"""

import io
import os
import struct
import sys
import urllib.parse
from concurrent.futures import ThreadPoolExecutor

from PIL import Image

from fetch import get
from geo import ORIGIN_LAT, ORIGIN_LON, utm_forward

HERE = os.path.dirname(os.path.abspath(__file__))
RAW = os.path.join(HERE, "raw")
BHALF = 40000.0
DN, DSP = 801, 100.0
IMG, TILES = 4096, 2


def fetch_dem(e0, n0):
    path = os.path.join(HERE, "backdrop_dem.f32")
    if os.path.exists(path):
        return
    q = urllib.parse.urlencode(
        {
            # Node grid: pixel edges half a cell outside the nodes.
            "bbox": f"{e0 - BHALF - DSP / 2},{n0 - BHALF - DSP / 2},{e0 + BHALF + DSP / 2},{n0 + BHALF + DSP / 2}",
            "bboxSR": 32610,
            "imageSR": 32610,
            "size": f"{DN},{DN}",
            "format": "bsq",
            "pixelType": "F32",
            "interpolation": "RSP_BilinearInterpolation",
            "f": "image",
        }
    )
    print("backdrop terrain...", file=sys.stderr)
    raw = get("https://elevation.nationalmap.gov/arcgis/rest/services/3DEPElevation/ImageServer/exportImage?" + q, tries=8)
    if len(raw) < DN * DN * 4:
        raise SystemExit(f"terrain: got {len(raw)} bytes: {raw[:200]!r}")
    dem = struct.unpack(f"<{DN * DN}f", raw[: DN * DN * 4])
    rows = [dem[(DN - 1 - j) * DN : (DN - j) * DN] for j in range(DN)]
    with open(path, "wb") as f:
        for r in rows:
            f.write(struct.pack(f"<{DN}f", *r))


def fetch_img_tile(e0, n0, tj, ti):
    path = os.path.join(RAW, f"backdrop_{TILES}_{tj}_{ti}.jpg")
    if os.path.exists(path):
        return path
    step = 2 * BHALF / TILES
    x0 = e0 - BHALF + ti * step
    y1 = n0 + BHALF - tj * step
    q = urllib.parse.urlencode(
        {
            "bbox": f"{x0},{y1 - step},{x0 + step},{y1}",
            "bboxSR": 32610,
            "imageSR": 32610,
            "size": f"{IMG // TILES},{IMG // TILES}",
            "format": "jpg",
            "compressionQuality": 90,
            "f": "image",
        }
    )
    data = get("https://imagery.nationalmap.gov/arcgis/rest/services/USGSNAIPImagery/ImageServer/exportImage?" + q, tries=8)
    Image.open(io.BytesIO(data)).verify()
    with open(path + ".part", "wb") as f:
        f.write(data)
    os.replace(path + ".part", path)
    print(f"  imagery tile {tj},{ti}", file=sys.stderr)
    return path


def main():
    os.makedirs(RAW, exist_ok=True)
    e0, n0 = utm_forward(ORIGIN_LON, ORIGIN_LAT)
    fetch_dem(e0, n0)
    print("backdrop imagery...", file=sys.stderr)
    jobs = [(tj, ti) for tj in range(TILES) for ti in range(TILES)]
    with ThreadPoolExecutor(4) as ex:
        paths = list(ex.map(lambda t: fetch_img_tile(e0, n0, *t), jobs))
    px = IMG // TILES
    img = Image.new("RGB", (IMG, IMG))
    for (tj, ti), path in zip(jobs, paths):
        img.paste(Image.open(path).convert("RGB").resize((px, px)), (ti * px, tj * px))
    out = os.path.join(HERE, "backdrop.jpg")
    img.save(out, quality=85, optimize=True)
    print(f"wrote backdrop_dem.f32 and {out} ({os.path.getsize(out) / 1e6:.1f} MB)", file=sys.stderr)


if __name__ == "__main__":
    main()
