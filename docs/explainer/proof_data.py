"""`python3 proof_data.py NAME RECORDING DUMP_DIR [--settle T] > media/proof-NAME.js`: RECORDING is a `--record` directory or its trace.jsonl."""

import json
import math
import pathlib
import sys

DT_TICK = 0.02
# The settling study's box (docs/escape-law-terminal.md), plus turn rate in rad/s.
BOX = {"v": 0.5, "vz": 0.5, "phi": 0.02, "track": 0.02, "om": 0.02}


def jsonl(path: pathlib.Path) -> list:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def pack(points: list, step: int) -> list:
    pts = points[::step]
    if points and pts[-1] != points[-1]:
        pts.append(points[-1])
    out, prev = [], (0, 0, 0)
    for p in pts:
        q = tuple(round(c * 10) for c in p)
        out += [q[0] - prev[0], q[1] - prev[1], q[2] - prev[2]]
        prev = q
    return out


def rollout_part(path: list, end: dict | None) -> list:
    """The rollout without the end set's continuation (73 helix points, or the ray's start and end)."""
    if end is None:
        return path
    return path[:-73] if end["kind"] == "helix" else path[:-2]


def settle_curve(s: dict) -> dict:
    rows = s["rows"]
    cols = {c: i for i, c in enumerate(s["cols"])}
    n = len(rows)
    om = []
    for i in range(n):
        a, b = rows[max(i - 1, 0)], rows[min(i + 1, n - 1)]
        om.append((b[cols["track"]] - a[cols["track"]]) / (b[0] - a[0]))
    last = [i for i in range(n) if rows[i][0] >= rows[-1][0] - 4.0]
    ref = {k: sum(rows[i][cols[k]] for i in last) / len(last) for k in ("v", "vz", "phi", "track")}
    ref["om"] = sum(om[i] for i in last) / len(last)
    straight = s["end"]["kind"] == "ray"
    pts = []
    for i in range(0, n, 4):  # every 0.25 s
        r = rows[i]
        parts = {
            "v": abs(r[cols["v"]] - ref["v"]) / BOX["v"],
            "vz": abs(r[cols["vz"]] - ref["vz"]) / BOX["vz"],
            "phi": abs(r[cols["phi"]] - ref["phi"]) / BOX["phi"],
            "om": abs(om[i] - ref["om"]) / BOX["om"],
        }
        if straight:
            parts["track"] = abs(r[cols["track"]] - ref["track"]) / BOX["track"]
        pts.append([round(r[0], 2), round(max(parts.values()), 3), round(r[cols["v"]], 2), round(r[cols["vz"]], 2), round(r[cols["z"]], 1)])
    t_settled = None
    for i in range(len(pts)):
        if all(p[1] <= 1.0 for p in pts[i:]):
            t_settled = pts[i][0]
            break
    return {
        "t": s["t"],
        "escape": s["escape"],
        "ref": {k: round(v, 4) for k, v in ref.items()},
        "secs": rows[-1][0],
        "t_settled": t_settled,
        "pts": pts,
    }


def main() -> None:
    name, rec, dump = sys.argv[1], pathlib.Path(sys.argv[2]), pathlib.Path(sys.argv[3])
    settle_t = float(sys.argv[sys.argv.index("--settle") + 1]) if "--settle" in sys.argv else None
    trace = jsonl(rec if rec.is_file() else rec / "trace.jsonl")
    ticks = {round(t["t"] / DT_TICK): t for t in jsonl(dump / "ticks.jsonl")}
    paths = {p["id"]: p for p in jsonl(dump / "paths.jsonl")}

    frames, used_paths, ends, end_ids = [], {}, [], {}
    for f in trace:
        k = round(f["sim_t"] / DT_TICK)
        t = ticks.get(k)
        if t is None:
            sys.exit(f"frame {f['frame']}: no tick at sim_t {f['sim_t']} in {dump}")
        if (f["mode"], f["escape"]) != (t["mode"], t["escape"]):
            sys.exit(f"frame {f['frame']}: recording says {f['mode']}/{f['escape']}, dump says {t['mode']}/{t['escape']}")
        end_key = json.dumps(t["end"], sort_keys=True)
        if end_key not in end_ids:
            end_ids[end_key] = len(ends)
            ends.append(t["end"])
        for pid, key in ((t["path"], "held"), (t["failed"], "failed")):
            if pid >= 0 and pid not in used_paths:
                p = paths[pid]["path"]
                used_paths[pid] = pack(rollout_part(p, t["end"]) if key == "held" else p, 2)
        vp = [float(f"{x:.6g}") for x in f["view_proj"]]
        frames.append([round(f["sim_t"], 2), f["mode"], f["escape"], [round(c, 2) for c in f["aircraft"]], vp, t["path"], t["failed"], end_ids[end_key], round(f["clear"], 2), [round(c, 1) for c in f["camera"]]])

    # Buildings near anything drawn: for occlusion and the plan inset.
    xs, ys = [], []
    for f in trace:
        xs += [f["aircraft"][0], f["camera"][0]]
        ys += [f["aircraft"][1], f["camera"][1]]
    for e in ends:
        if e and e["kind"] == "helix":
            r1 = e["r"] + e["m"] + 4.5
            xs += [e["c"][0] - r1, e["c"][0] + r1]
            ys += [e["c"][1] - r1, e["c"][1] + r1]
        elif e:
            xs += [e["p"][0], e["end"][0]]
            ys += [e["p"][1], e["end"][1]]
    pad = 300.0
    x0, x1, y0, y1 = min(xs) - pad, max(xs) + pad, min(ys) - pad, max(ys) + pad
    boxes = [
        [round(b[0], 1), round(b[1], 1), round(b[2], 1), round(b[3], 1), round(b[4], 1), round(b[5], 1)]
        for b in json.loads((dump / "boxes.json").read_text())
        if b[1] > x0 and b[0] < x1 and b[3] > y0 and b[2] < y1
    ]

    runs, start = [], None
    for k in sorted(ticks):
        t = ticks[k]
        if t["mode"] == "escape" and start is None:
            start = t["t"]
        elif t["mode"] != "escape" and start is not None:
            runs.append([start, t["t"]])
            start = None
    if start is not None:
        runs.append([start, None])
    data = {
        "name": name,
        "runs": runs,
        "fps": 30,
        "size": trace[0]["viewport"],
        "frames": frames,
        "paths": used_paths,
        "ends": ends,
        "boxes": boxes,
    }
    if settle_t is not None:
        s = next((s for s in jsonl(dump / "settle.jsonl") if abs(s["t"] - settle_t) < 0.011), None)
        if s is None:
            sys.exit(f"no takeover at {settle_t} s in {dump}/settle.jsonl")
        data["settle"] = settle_curve(s)
    sys.stdout.write("(window.PROOF_CLIPS = window.PROOF_CLIPS || {})[" + json.dumps(name) + "] = " + json.dumps(data, separators=(",", ":")) + ";\n")


if __name__ == "__main__":
    main()
