"""Close-call players: turn `cityflight --record` captures into the page's clips, posters, traces and chart data.

Usage: python3 -I cc_data.py REC_DIR [NAME ...], or python3 -I cc_data.py --from-traces [NAME ...] to rebuild only the
chart data from the committed media/traces/cc-NAME.trace.jsonl (no captures needed, nothing re-encoded).

REC_DIR holds one capture directory per clip (frame_*.png, frames.csv, trace.jsonl, args.txt), as written by
record_clips.sh. For each NAME (default: every capture directory) this writes media/cc-NAME.mp4 (H.264 at 1280 px, CRF 28,
a keyframe every 0.5 s for responsive scrubbing, faststart), media/cc-NAME.jpg (the frame at the closest moment)
and media/traces/cc-NAME.trace.jsonl (the recorder's per-frame trace); a run that crashes is cut 2 s after contact, then rewrites the CC_DATA
block in index.html with each clip's clearance-over-time trace.
"""
import csv
import json
import pathlib
import re
import shutil
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
FFMPEG = shutil.which("ffmpeg") or "/opt/homebrew/bin/ffmpeg"
MODES = {"pilot": 0, "free": 0, "blend": 1, "commit": 2, "escape": 2, "off": 3}


def trace_rows(name: str) -> list:
    """A committed clip trace as frames.csv rows."""
    out = []
    for line in (HERE / "media" / "traces" / f"cc-{name}.trace.jsonl").read_text().splitlines():
        f = json.loads(line)
        out.append({k: str(f[k]) for k in ("t", "sim_t", "clear", "min_clear", "mode", "png")} | {"crashed": "1" if f["crashed"] else "0"})
    return out


def clip(rec: pathlib.Path | None, name: str, encode: bool) -> dict:
    d = rec / name if rec else None
    rows = trace_rows(name) if d is None else list(csv.DictReader(open(d / "frames.csv")))
    # A run that crashes ends 2 s after contact: the rest is the frozen crash screen.
    k = next((i for i, r in enumerate(rows) if r["crashed"] == "1"), None)
    if k is not None:
        rows = rows[: k + 60]
    fps = 30.0
    t0 = float(rows[0]["t"])
    pts = []
    for i, r in enumerate(rows):
        pts.append([round(i / fps, 3), round(float(r["clear"]), 3), MODES[r["mode"]], int(r["crashed"])])
    # The running minimum is exact (every 20 ms tick); the frame where it last drops is the closest moment's frame.
    lo = float(rows[-1]["min_clear"])
    k_min = next(i for i, r in enumerate(rows) if float(r["min_clear"]) <= lo)
    k_crash = next((i for i, p in enumerate(pts) if p[3]), None)
    if k_crash is not None:
        k_min = k_crash
    keep = [p[:3] for i, p in enumerate(pts) if i % 2 == 0 or i == k_min or i == k_crash or i == len(pts) - 1]
    if encode:
        media = HERE / "media"
        (media / "traces").mkdir(parents=True, exist_ok=True)
        subprocess.run([FFMPEG, "-v", "error", "-y", "-framerate", str(fps), "-i", str(d / "frame_%05d.png"),
                        "-frames:v", str(len(rows)),
                        "-vf", "scale=1280:-2", "-c:v", "libx264", "-preset", "slow", "-crf", "28", "-g", "15",
                        "-keyint_min", "15", "-sc_threshold", "0", "-pix_fmt", "yuv420p", "-movflags", "+faststart",
                        str(media / f"cc-{name}.mp4")], check=True)
        subprocess.run([FFMPEG, "-v", "error", "-y", "-i", str(d / rows[k_min]["png"]), "-vf", "scale=1280:-2",
                        "-q:v", "4", str(media / f"cc-{name}.jpg")], check=True)
        lines = open(d / "trace.jsonl").read().splitlines()[: len(rows)]
        (media / "traces" / f"cc-{name}.trace.jsonl").write_text("\n".join(lines) + "\n")
    return {
        "dur": round(len(pts) / fps, 3),
        "t0": round(t0, 3),
        "min": [pts[k_min][0], round(lo, 3)],
        "crash": pts[k_crash][0] if k_crash is not None else None,
        "sim_crash": round(float(rows[k_crash]["sim_t"]), 2) if k_crash is not None else None,
        "rows": keep,
    }


def main() -> None:
    if sys.argv[1] == "--from-traces":
        rec = None
        names = [a for a in sys.argv[2:] if not a.startswith("--")] or sorted(p.name[3:-len(".trace.jsonl")] for p in (HERE / "media" / "traces").glob("cc-*.trace.jsonl"))
    else:
        rec = pathlib.Path(sys.argv[1])
        names = [a for a in sys.argv[2:] if not a.startswith("--")] or sorted(p.name for p in rec.iterdir() if (p / "frames.csv").exists())
    page = HERE / "index.html"
    html = page.read_text()
    m = re.search(r"/\*CC\*/const CC_DATA = (.*?);\n", html)
    data = json.loads(m.group(1)) if m else {}
    for n in names:
        data[n] = clip(rec, n, encode=rec is not None and "--no-encode" not in sys.argv)
        c = data[n]
        print(f"{n}: {c['dur']} s, min {c['min'][1]} m at {c['min'][0]} s, crash {c['crash']}")
    blob = "/*CC*/const CC_DATA = " + json.dumps(data, separators=(",", ":")) + ";\n"
    html = html.replace(m.group(0), blob) if m else html.replace("<!--CC_DATA-->", "<script>" + blob + "</script>")
    page.write_text(html)


if __name__ == "__main__":
    main()
