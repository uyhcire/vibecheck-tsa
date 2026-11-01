"""Download the CC0 ambientCG texture sets and pack them for the photoreal renderer.

Usage: python3 -I fetch.py   (needs Pillow; writes <set>/albedo.jpg, normal.jpg, orm.jpg here)
orm.jpg packs R = ambient occlusion, G = roughness, B = metalness.
"""

import io
import os
import sys
import tempfile
import urllib.request
import zipfile

from PIL import Image

SETS = {
    "facade_glass": "Facade001",
    "facade_grid": "Facade006",
    "facade_office": "Facade012",
    "facade_brick": "Facade018A",
    "facade_stone": "Facade019A",
    "facade_brown": "Facade020A",
    "asphalt": "Asphalt033",
    "grass": "Grass004",
    "rock": "Rock030",
    "concrete": "Concrete034",
    "gravel": "Gravel023",
}
SIZE = 1024
HERE = os.path.dirname(os.path.abspath(__file__))


def fetch(asset, tmp):
    url = f"https://ambientcg.com/get?file={asset}_1K-JPG.zip"
    path = os.path.join(tmp, f"{asset}.zip")
    req = urllib.request.Request(url, headers={"User-Agent": "cityflight-fetch"})
    with urllib.request.urlopen(req) as r, open(path, "wb") as f:
        f.write(r.read())
    maps = {}
    with zipfile.ZipFile(path) as z:
        for name in z.namelist():
            if not name.lower().endswith((".jpg", ".jpeg", ".png")):
                continue
            key = name.rsplit("_", 1)[-1].rsplit(".", 1)[0]
            maps[key] = Image.open(io.BytesIO(z.read(name)))
    return maps


def grey(img, default):
    if img is None:
        return Image.new("L", (SIZE, SIZE), default)
    return img.convert("L").resize((SIZE, SIZE), Image.LANCZOS)


def main():
    with tempfile.TemporaryDirectory() as tmp:
        for name, asset in SETS.items():
            print(name, asset, file=sys.stderr)
            m = fetch(asset, tmp)
            out = os.path.join(HERE, name)
            os.makedirs(out, exist_ok=True)
            m["Color"].convert("RGB").resize((SIZE, SIZE), Image.LANCZOS).save(os.path.join(out, "albedo.jpg"), quality=85)
            m["NormalGL"].convert("RGB").resize((SIZE, SIZE), Image.LANCZOS).save(os.path.join(out, "normal.jpg"), quality=90)
            orm = Image.merge("RGB", (grey(m.get("AmbientOcclusion"), 255), grey(m.get("Roughness"), 160), grey(m.get("Metalness"), 0)))
            orm.save(os.path.join(out, "orm.jpg"), quality=90)
            print("  maps:", sorted(m), file=sys.stderr)


if __name__ == "__main__":
    main()
