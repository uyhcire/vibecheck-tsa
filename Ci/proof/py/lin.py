import numpy as np
from pf import *
t5 = np.load("traj_5.npy"); t36 = np.load("traj_3600.npy")
# coordinates in z: all but x(0), h(1), stall(11)
ZI = [i for i in range(21) if i not in (0, 1, 11)]
STEP = {2:6554, 3:6554, 4:66, 5:655, 6:655, 7:655360, 8:6554, 9:6554, 10:6554, 12:6554, 13:6554, 14:6554,
        15:6554, 16:6554, 17:6554, 18:6554, 19:655, 20:655}
def manifold_at(h):
    """nearest on-manifold sample (raw) for altitude h (m)"""
    hs = t5[300:, 1] / 65536
    if h <= hs.max() - 1:
        k = 300 + np.argmin(abs(hs - h)); return t5[k].copy()
    hs2 = t36[600:, 1] / 65536
    k = 600 + np.argmin(abs(hs2 - h)); return t36[k].copy()
def jac(x0):
    pts = []
    for i in ZI:
        for sgn in (1, -1):
            p = x0.copy(); p[i] += sgn * STEP[i]; pts.append(p)
    img, _, _ = ticks(np.array(pts))
    J = np.zeros((len(ZI), len(ZI))); dh = np.zeros(len(ZI))
    for a, i in enumerate(ZI):
        d = (img[2*a] - img[2*a+1]) / (2 * STEP[i])
        J[:, a] = [d[j] for j in ZI]; dh[a] = d[1]
    return J, dh
if __name__ == "__main__":
    for h in [100, 500, 1000, 2000, 2500, 3000, 3250, 3313, 3400, 3500]:
        x0 = manifold_at(h)
        J, dh = jac(x0)
        ev = np.linalg.eigvals(J); ev = ev[np.argsort(-abs(ev))]
        print(f"h {h} (sample h {x0[1]/65536:.1f}, vz {x0[3]/65536:.3f}):", " ".join(f"{abs(e):.4f}{'c' if abs(e.imag)>1e-9 else ''}" for e in ev[:9]))
