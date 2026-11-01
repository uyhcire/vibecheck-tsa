import numpy as np, lin
from pf import *
from lin import ZI, STEP, jac
Mall = np.load("man2.npy"); hs = Mall[:,1]/65536
def nearest(h): return Mall[np.argmin(abs(hs-h))].copy()
S = np.array([STEP[i] for i in ZI], dtype=float)
HN = np.arange(0, 2800, 100); Js = []
for h in HN:
    row = []
    for scale in [1, 4]:
        lin.STEP = {k: v*scale for k, v in STEP.items()}
        J, _ = jac(nearest(max(h, 20))); row.append(np.diag(1/S) @ J @ np.diag(S))
    lin.STEP = dict(STEP); Js.append(row)
np.save("JfN.npy", np.array(Js))
