"""Numerics helpers: batch one-tick evaluation through the compiled Fx model (pfprobe)."""
import subprocess, numpy as np, os
HERE = os.path.dirname(os.path.abspath(__file__))
EXE = os.path.join(HERE, "..", "harness", ".lake", "build", "bin", "pfprobe")
NAMES = ["x","h","vx","vz","dx","dz","q","rpm","tmap","udot","wdot","stall","ah","au","qd","ah1","au1","pvz","pvz2","eI","ac"]

def ticks(points, k=1):
    """points: (N,21) int array -> (N,21) image, safe[N], climb[N]."""
    inp = "\n".join(" ".join(str(int(v)) for v in p) for p in points) + "\n"
    out = subprocess.run([EXE, "tick", str(k)], input=inp, capture_output=True, text=True, check=True).stdout
    rows = [l.split() for l in out.strip().split("\n")]
    img = np.array([[int(v) for v in r[:21]] for r in rows], dtype=np.int64)
    safe = np.array([r[21] == "true" for r in rows]); cl = np.array([r[22] == "true" for r in rows])
    return img, safe, cl

def bench_traj(i, n):
    out = subprocess.run([EXE, "bench", str(i), str(n)], capture_output=True, text=True, check=True,
                         cwd=os.path.join(HERE, "..", "harness")).stdout
    rows = [l.split() for l in out.strip().split("\n")]
    return np.array([[int(v) for v in r[1:22]] for r in rows], dtype=np.int64), [r[22] == "true" for r in rows]

def traj(x, n):
    inp = " ".join(str(int(v)) for v in x) + "\n"
    out = subprocess.run([EXE, "traj", str(n)], input=inp, capture_output=True, text=True, check=True).stdout
    rows = [l.split() for l in out.strip().split("\n")]
    return np.array([[int(v) for v in r[1:22]] for r in rows], dtype=np.int64)

def ticks_T(points, k=1):
    """-> image, safe, climb, inT(before), inT(after)"""
    inp = "\n".join(" ".join(str(int(v)) for v in p) for p in points) + "\n"
    out = subprocess.run([EXE, "tick", str(k)], input=inp, capture_output=True, text=True, check=True).stdout
    rows = [l.split() for l in out.strip().split("\n")]
    img = np.array([[int(v) for v in r[:21]] for r in rows], dtype=np.int64)
    b = lambda j: np.array([r[j] == "true" for r in rows])
    return img, b(21), b(22), b(23), b(24)

def frozen(points, n):
    inp = "\n".join(" ".join(str(int(v)) for v in p) for p in points) + "\n"
    out = subprocess.run([EXE, "frozen", str(n)], input=inp, capture_output=True, text=True, check=True).stdout
    return np.array([[int(v) for v in l.split()[:21]] for l in out.strip().split("\n")], dtype=np.int64)
