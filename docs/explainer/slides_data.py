"""`slides_data.py TRAJ_DIR FAN_DIR DOME_DIR > media/slides-data.js`: the pilots-from-one-start runs, the candidate fan and the dome, for the slides."""

import json
import math
import pathlib
import struct
import sys

LABEL = {"straight": "straight climb", "left": "climbing turn L 30°", "right": "climbing turn R 30°",
         "left40": "L 40°", "right40": "R 40°", "street": "follow street"}


def jsonl(path: pathlib.Path) -> list:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def traj(d: pathlib.Path) -> dict:
    runs = {"on": [], "off": []}
    boxes = json.loads(next(d.glob("*-on/boxes.json")).read_text())
    for run in sorted(p for p in d.iterdir() if p.is_dir()):
        kind, side = run.name.rsplit("-", 1)
        ticks = jsonl(run / "ticks.jsonl")
        pts = [[round(t["pos"][0]), round(t["pos"][1])] for i, t in enumerate(ticks) if i % 10 == 9 or i == len(ticks) - 1]
        last = ticks[-1]
        crash = [round(last["pos"][0], 1), round(last["pos"][1], 1), last["t"]] if last.get("crashed") or last["clear"] < 0 else None
        runs[side].append({"pilot": kind, "pts": pts, "crash": crash, "min": round(min(t["clear"] for t in ticks), 2)})
    xs = [p[0] for side in runs.values() for r in side for p in r["pts"]]
    ys = [p[1] for side in runs.values() for r in side for p in r["pts"]]
    pad = 150
    win = [min(xs) - pad, max(xs) + pad, min(ys) - pad, max(ys) + pad]
    near = [[round(b[0]), round(b[1]), round(b[2]), round(b[3]), round(b[5])] for b in boxes
            if b[1] > win[0] and b[0] < win[1] and b[3] > win[2] and b[2] < win[3]]
    start = jsonl(next(d.glob("*-on/ticks.jsonl")))[0]["pos"]
    return {"runs": runs, "boxes": near, "win": win, "start": [round(start[0]), round(start[1]), round(start[2])]}


def fan(d: pathlib.Path) -> list:
    out = []
    for f in jsonl(d / "fan.jsonl"):
        cands = []
        for c in f["cands"]:
            path = c["path"][: len(c["path"]) - c["tail"]] if c["tail"] else c["path"]
            cands.append({"order": c["order"], "escape": c["escape"], "label": LABEL.get(c["escape"], c["escape"]),
                          "resumed": c["resumed"], "outcome": c["outcome"], "min_clear": c["min_clear"], "t": c["t"],
                          "path": [[round(q[0], 1), round(q[1], 1), round(q[2], 1)] for q in path[::2] + path[-1:]]})
        out.append({k: f[k] for k in ("t", "holding", "cand_clear", "found", "accepted", "mode")} | {"cands": cands})
    return out


def dome(d: pathlib.Path) -> dict:
    out = {}
    for r in (143, 250):
        h = json.loads((d / f"dome_r{r}.json").read_text())
        raw = (d / h["file"]).read_bytes()
        nx, ny = h["nx"], h["ny"]
        vals = struct.unpack(f"<{nx * ny}f", raw)
        step, half = 4, 1300  # 40 m nodes over the city square
        i0 = int((-half - h["origin"][0]) / h["spacing"])
        i1 = int((half - h["origin"][0]) / h["spacing"])
        grid = [[round(vals[j * nx + i]) for i in range(i0, i1 + 1, step)] for j in range(i0, i1 + 1, step)]
        out[str(r)] = {"x0": h["origin"][0] + i0 * h["spacing"], "dx": h["spacing"] * step, "n": len(grid), "z": grid,
                       "z_top": h["z_top"], "m": h["m"]}
    return out


def main() -> None:
    t, f, dm = map(pathlib.Path, sys.argv[1:4])
    data = {"traj": traj(t), "fan": fan(f), "dome": dome(dm)}
    sys.stdout.write("window.SLIDES = " + json.dumps(data, separators=(",", ":")) + ";\n")


if __name__ == "__main__":
    main()
