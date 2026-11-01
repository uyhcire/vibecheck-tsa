"""Provable cell boxes: slow deviations bounded by LDL-certifiable constants per 100 m node interval
(d_k² ≤ c = Rb (P⁻¹)_kk at both nodes), fast fields by |G|·B plus the tolerance parts, with integer floors."""
import numpy as np, re, sys
src = open("../TData.lean").read()
def arr(name):
    m = re.search(rf"^def {name} : Array Int := (#\[.*\])$", src, re.M); return [int(v) for v in re.findall(r"-?\d+", m.group(1))]
def mat(name):
    m = re.search(rf"^def {name} : Array \(Array Int\) := (#\[.*\])$", src, re.M)
    return [[int(v) for v in r.split(",")] for r in re.findall(r"#\[([-\d, ]+)\]", m.group(1))]
def tabref(name):
    m = re.search(rf"^def {name} : Array \(Array (?:\(Array )?Int\)?\)? := #\[(.*)\]$", src, re.M)
    return [x.strip() for x in m.group(1).split(",")]
r2 = arr("r2Tab") if "def r2Tab : Array Int" in src else None
m = re.search(r"^def r2Tab : Array Int := (#\[.*\])$", src, re.M); r2 = [int(v) for v in re.findall(r"-?\d+", m.group(1))]
P = [mat(f"p{n}") for n in range(28)]
G = [mat(f"g{n}") for n in range(28)]
m = re.search(r"^def tkTab : Array Int := (#\[.*\])$", src, re.M); tk = [int(v) for v in re.findall(r"-?\d+", m.group(1))]
def m2(name):
    m = re.search(rf"^def {name} : Array \(Array Int\) := #\[(.*)\]$", src, re.M)
    return [[int(v) for v in r.split(",")] for r in re.findall(r"#\[([-\d, ]+)\]", m.group(1))]
kb = m2("kbTab"); tp = m2("tpTab")
cent = [arr(f"c{n}") for n in range(1351)]
box = [arr(f"b{n}") for n in range(267)]
fields = [int(v) for v in re.findall(r"\d+", re.search(r"^def fields : Array Nat := (#\[.*\])$", src, re.M).group(1))]
B = []
for i in range(27):
    Rb = max(r2[i], r2[i + 1]) + 1
    c = [Rb * max(np.linalg.inv(np.array(P[i], float))[k, k], np.linalg.inv(np.array(P[i + 1], float))[k, k]) * 1.001 for k in range(7)]
    B.append([int(np.ceil(np.sqrt(ck))) + 1 for ck in c])
def pbox(ci):
    a = 10 + 10 * ci; b = min(a + 10, 2680); j = a // 100
    rows = range(a // 2, b // 2 + 1)
    lo, hi = {}, {}
    Bj = B[j]
    for k in range(17):
        cv = [cent[rr][k] for rr in rows]
        if k < 7:
            w = Bj[k]
        else:
            kk = k - 7
            gsum = max(sum(abs(G[jj][kk][i]) * Bj[i] for i in range(7)) for jj in (j, j + 1)) // 2**20 + 3
            lam = max(tk[j], tk[j + 1]) * max(abs(kb[j][kk]), abs(kb[j + 1][kk])) // 2**50 + 2
            w = gsum + lam + max(tp[j][kk], tp[j + 1][kk]) + 2
        lo[fields[k]] = min(cv) - w - 1; hi[fields[k]] = max(cv) + w + 1
    return lo, hi
if __name__ == "__main__":
    for ci in [0, 99, 199, 240, 266]:
        lo, hi = pbox(ci); b = box[ci]
        print(ci, " ".join(f"{f}:{(hi[f]-lo[f]) / max(1, (b[19+f]-b[f]) if f < 19 else (b[39]-b[38])):.2f}" for f in sorted(lo)))

def cellbox_prov(ci):
    a = 10 + 10 * ci; b = min(a + 10, 2680)
    lo, hi = pbox(ci)
    L = [0] * 19; H = [0] * 19
    L[0], H[0] = -2**40, 2**40; L[1], H[1] = a * 65536, b * 65536; L[11] = H[11] = 0
    for f in lo:
        if f < 19: L[f], H[f] = lo[f], hi[f]
    return L, H, lo[19], hi[19]
