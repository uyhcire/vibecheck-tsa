import numpy as np
from pf import *
M = np.load("manifold.npy")
x = M[np.argmin(abs(M[:,1]/65536 - 90))].copy(); x[0] = 0
for it in range(3):
    x[1] = 5 * 65536 + 32768
    t = traj(x, 400)
    k = np.argmin(abs(t[:,1]/65536 - 40)); x = t[k].copy(); x[0] = 0
    print(it, [(round(t[j,1]/65536,1), round(t[j,2]/65536,4), round(t[j,3]/65536,4), t[j,19]) for j in [0, 20, 50, 100, 150, 200, 300]])
np.save("traj_low.npy", t)
