import numpy as np, sys
from pf import *
tr, _ = bench_traj(0, 600)
x0 = tr[500].copy()
# coordinates to perturb (exclude x=0, stall=11)
idx = [i for i in range(21) if i not in (0, 11)]
step = {1:65536, 2:6554, 3:6554, 4:66, 5:655, 6:655, 7:655360, 8:6554, 9:6554, 10:6554, 12:6554, 13:6554, 14:6554,
        15:6554, 16:6554, 17:6554, 18:6554, 19:655, 20:655}
pts = []
for i in idx:
    for sgn in (1, -1):
        p = x0.copy(); p[i] += sgn * step[i]; pts.append(p)
pts.append(x0)
img, safe, cl = ticks(np.array(pts))
f0 = img[-1]
J = np.zeros((len(idx), len(idx)))
for a, i in enumerate(idx):
    d = (img[2*a] - img[2*a+1]) / (2 * step[i])
    J[:, a] = [d[j] for j in idx]
np.save("J.npy", J); np.save("x0.npy", x0)
ev = np.linalg.eigvals(J)
ev = ev[np.argsort(-abs(ev))]
for e in ev: print(f"{e.real:+.5f} {e.imag:+.5f}  |{abs(e):.5f}|  ang {np.angle(e):+.4f}")
print("drift f(x0)-x0:", {NAMES[j]: int(f0[j]-x0[j]) for j in idx})
