"""`media.py [--jobs N] [--write-lock] [--only A,B]`: rebuild the page's media from clips.json; hashes must match clips.lock.json."""

import concurrent.futures
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
MEDIA = HERE / "media"
REC = pathlib.Path(os.environ.get("REC", "/tmp/explainer-rec"))
DUMP = pathlib.Path(os.environ.get("PROOF_DUMP", "/tmp/explainer-dump"))
BIN = ROOT / "flight" / "target" / "release"
FFMPEG = shutil.which("ffmpeg") or "/opt/homebrew/bin/ffmpeg"
WINDOW_KEYS = ("viewport", "view_proj")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def trace_hash(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    for line in path.read_text().splitlines():
        if line.strip():
            f = json.loads(line)
            for k in WINDOW_KEYS:
                f.pop(k, None)
            h.update((json.dumps(f, sort_keys=True, separators=(",", ":")) + "\n").encode())
    return h.hexdigest()


def run(cmd: list, log: pathlib.Path, cwd: pathlib.Path) -> None:
    with open(log, "w") as out:
        if subprocess.run(cmd, cwd=cwd, stdout=out, stderr=subprocess.STDOUT).returncode != 0:
            sys.exit(f"failed: {' '.join(map(str, cmd))} (log: {log})")


def record(r: dict) -> dict:
    out = REC / r["name"]
    shutil.rmtree(out, ignore_errors=True)
    out.parent.mkdir(parents=True, exist_ok=True)
    args = ["--safety-filter", "exact-rollout", *r["args"], "--record", str(out), "--frames", str(r["frames"]),
            "--record-from", str(r["from"]), "--record-every", str(r["every"]), "--record-scale", str(r["scale"])]
    t0 = time.time()
    run(["nice", "-n", "5", str(BIN / "cityflight"), *args], REC / f"{r['name']}.log", ROOT / "flight")
    print(f"  recorded {r['name']} in {time.time() - t0:.0f} s", flush=True)
    return {"frames_csv": sha((out / "frames.csv").read_bytes()), "trace": trace_hash(out / "trace.jsonl"), "code": CODE["HEAD"]}


def dump(d: dict) -> dict:
    out = DUMP / d["name"]
    shutil.rmtree(out, ignore_errors=True)
    out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    run([str(BIN / "proofdump"), str(out), d["run"], *d["args"]], DUMP / f"{d['name']}.log", ROOT / "flight")
    print(f"  replayed {d['name']} in {time.time() - t0:.0f} s", flush=True)
    return {"ticks": sha((out / "ticks.jsonl").read_bytes()), "code": CODE["HEAD"]}


def ffmpeg(*args) -> None:
    subprocess.run([FFMPEG, "-loglevel", "error", "-y", *map(str, args)], check=True)


def hero(r: dict) -> None:
    # The page pins its callout at (40.5%, 56.4%) of the hero.
    f = json.loads((REC / r["name"] / "trace.jsonl").read_text().splitlines()[0])
    w, h = f["viewport"]
    m, (x, y, z) = f["view_proj"], f["aircraft"]
    cw = m[3] * x + m[7] * y + m[11] * z + m[15]
    sx = ((m[0] * x + m[4] * y + m[8] * z + m[12]) / cw + 1) / 2 * w
    sy = (1 - (m[1] * x + m[5] * y + m[9] * z + m[13]) / cw) / 2 * h
    ch = min(h, round(w * 9 / 16)) // 2 * 2
    cwid = round(ch * 16 / 9) // 2 * 2
    ox = int(max(0, min(w - cwid, sx - 0.405 * cwid)))
    oy = int(max(0, min(h - ch, sy - 0.564 * ch)))
    ffmpeg("-i", REC / r["name"] / "frame_00000.png", "-vf", f"crop={cwid}:{ch}:{ox}:{oy},scale=1600:900:flags=lanczos", "-q:v", "3", MEDIA / "hero-tower-gap.jpg")


CODE: dict = {}


def main() -> None:
    spec = json.loads((HERE / "clips.json").read_text())
    lock_path = HERE / "clips.lock.json"
    write = "--write-lock" in sys.argv
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 1
    only = set(sys.argv[sys.argv.index("--only") + 1].split(",")) if "--only" in sys.argv else None
    for b in ("cityflight", "proofdump"):
        if not (BIN / b).exists():
            sys.exit(f"{BIN / b} is missing: build it first (make present-media does)")
    lock = json.loads(lock_path.read_text()) if lock_path.exists() else {}
    if not write and not lock:
        sys.exit("no clips.lock.json to check against (make it with --write-lock)")
    recs = [r for r in spec["recordings"] if not only or r["name"] in only]
    dumps = [d for d in spec["dumps"] if not only or d["name"] in only]
    t_start = time.time()
    CODE["HEAD"] = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    print(f"recording {len(recs)} clips and replaying {len(dumps)} runs ({jobs} at a time) into {REC} and {DUMP}", flush=True)
    with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        got = dict(zip([r["name"] for r in recs], pool.map(record, recs)))
        got |= {"dump:" + d["name"]: h for d, h in zip(dumps, pool.map(dump, dumps))}

    if write:
        lock = {"note": "frames.csv; trace.jsonl less viewport and view_proj; proofdump ticks.jsonl; code: the commit each was made at", "hashes": {**lock.get("hashes", {}), **got}}
        lock_path.write_text(json.dumps(lock, indent=1, sort_keys=True) + "\n")
        print(f"wrote {lock_path.name}")
    else:
        bad = [f"{k}: {f} is {v[:12]}, expected {lock['hashes'].get(k, {}).get(f, 'nothing')[:12]} (made at {lock['hashes'].get(k, {}).get('code', '?')[:10]})"
               for k, h in got.items() for f, v in h.items() if f != "code" and lock["hashes"].get(k, {}).get(f) != v]
        if bad:
            print("HASH MISMATCH: the simulation no longer reproduces these clips; the code changed since they were made:\n  "
                  + "\n  ".join(bad), file=sys.stderr)
            sys.exit(1)
        print(f"all {sum(len(h) - 1 for h in got.values())} hashes match clips.lock.json")

    MEDIA.mkdir(exist_ok=True)
    names = {r["name"] for r in recs}
    cc = [r["name"] for r in recs if r["group"] == "close-call"]
    if cc:
        subprocess.run([sys.executable, "-I", HERE / "cc_data.py", REC, *cc], check=True)
    for r in recs:
        if r["group"] == "proof":
            n = r["name"]
            ffmpeg("-framerate", 30, "-i", REC / n / "frame_%05d.png", "-vf", "scale=1280:768:flags=lanczos", "-c:v", "libx264",
                   "-preset", "slow", "-crf", 28, "-g", 10, "-pix_fmt", "yuv420p", "-movflags", "+faststart", MEDIA / f"{n}.mp4")
            ffmpeg("-i", REC / n / f"frame_{spec['posters'][n]:05d}.png", "-vf", "scale=1280:768", "-q:v", 4, MEDIA / f"{n}.jpg")
            p = spec["proof_data"][n]
            cmd = [sys.executable, "-I", HERE / "proof_data.py", n.removeprefix("proof-"), REC / n / "trace.jsonl", DUMP / p["dump"]]
            if "settle" in p:
                cmd += ["--settle", str(p["settle"])]
            with open(MEDIA / f"{n}.js", "w") as out:
                subprocess.run(cmd, stdout=out, check=True)
        elif r["name"] == "paths":
            for jpg, png in r["stills"].items():
                ffmpeg("-i", REC / "paths" / png, "-vf", "scale=1280:768", "-q:v", 4, MEDIA / jpg)
        elif r["name"] == "hero":
            hero(r)
    if names & {"towergap", "towergap-off"}:
        for side, src in (("on", "cc-towergap.mp4"), ("off", "cc-towergap-off.mp4")):
            ffmpeg("-ss", 1.7, "-i", MEDIA / src, "-t", 4.6, "-an", "-c:v", "libx264", "-preset", "slow", "-crf", 28, "-g", 15,
                   "-pix_fmt", "yuv420p", "-movflags", "+faststart", MEDIA / f"tower-gap-{side}.mp4")
            ffmpeg("-ss", 4.0, "-i", MEDIA / src, "-frames:v", 1, "-q:v", 4, MEDIA / f"tower-gap-{side}.jpg")
    if (DUMP / "showcase" / "ticks.jsonl").exists() and (DUMP / "showcase-off" / "ticks.jsonl").exists():
        subprocess.run([sys.executable, "-I", HERE / "plate_data.py", DUMP / "showcase", DUMP / "showcase-off"], check=True)
    print(f"done in {(time.time() - t_start) / 60:.1f} min")


if __name__ == "__main__":
    main()
