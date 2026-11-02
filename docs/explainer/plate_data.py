"""Inline the Tower gap plate data into index.html from `make proofdump` runs: `plate_data.py ON_DIR OFF_DIR` (RUN=showcase, and with ARGS=--off)."""

import json
import pathlib
import re
import sys

T_MAX = 9.0
WIN = (-560.0, 80.0, -120.0, 560.0)  # x0, x1, y0, y1 (m), map axes: x east, y north


def jsonl(path: pathlib.Path) -> list:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


MODE = {"pilot": 0, "blend": 1, "escape": 2, "off": 3}


def track(ticks: list) -> list:
    """Every fifth tick (0.1 s) and the last: [t, x, y, z, clearance, mode]."""
    rows = [r for i, r in enumerate(ticks) if (i % 5 == 4 or i == len(ticks) - 1) and r["t"] <= T_MAX + 1e-9]
    return [[r["t"], round(r["pos"][0], 1), round(r["pos"][1], 1), round(r["pos"][2], 1), round(r["clear"], 2), MODE[r["mode"]]] for r in rows]


def main() -> None:
    on_dir, off_dir = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
    on, off = jsonl(on_dir / "ticks.jsonl"), jsonl(off_dir / "ticks.jsonl")
    x0, x1, y0, y1 = WIN
    boxes = sorted(
        (
            [round(b[0]), round(b[1]), round(b[2]), round(b[3]), round(b[5] - b[4]), round(b[5], 1)]
            for b in json.loads((on_dir / "boxes.json").read_text())
            if b[1] > x0 and b[0] < x1 and b[3] > y0 and b[2] < y1
        ),
        key=lambda b: b[4],
    )
    unique = [b for i, b in enumerate(boxes) if b not in boxes[:i]]
    first = next(r for r in on if r["mode"] == "escape")
    held = next(p for p in jsonl(on_dir / "paths.jsonl") if p["id"] == first["path"])
    plans = [{"t": first["t"], "path": [[round(q[0]), round(q[1]), round(q[2])] for q in held["path"][::3]]}]
    lo = min(on, key=lambda r: r["clear"])
    data = {
        "on": track(on),
        "off": track(off),
        "plans": plans,
        "boxes": unique,
        "win": WIN,
        "min_on": [round(lo["clear"], 2), lo["t"]],
        "crash_off": off[-1]["t"],
    }
    html = pathlib.Path(__file__).with_name("index.html")
    text = html.read_text()
    blob = "const PLATE = " + json.dumps(data, separators=(",", ":")) + ";"
    text, n = re.subn(r"(/\*PLATE\*/).*?(/\*END\*/)", lambda m: m.group(1) + blob + m.group(2), text, flags=re.S)
    assert n == 1, "placeholder /*PLATE*/.../*END*/ not found"
    html.write_text(text)
    print(f"{len(data['on'])} on rows, {len(data['off'])} off rows, {len(unique)} boxes, {len(plans)} plans")


if __name__ == "__main__":
    main()
