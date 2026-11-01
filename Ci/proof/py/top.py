import numpy as np
from pf import *
t5 = np.load("traj_5.npy")
x = t5[9000].copy(); x[0]=0   # on manifold ~2200 m
F = lambda r: r/65536
t = traj(x, 20000)
for k in [0,500,1000,1500,2000,2500,3000,4000,6000,10000,20000]:
    r=t[k]; print(f"k {k} h {F(r[1]):.1f} vx {F(r[2]):.3f} vz {F(r[3]):.3f} rpm {F(r[7]):.0f} tmap {F(r[8]):.2f} eI {r[19]} ac {r[20]} q {r[6]}")
np.save("traj_top.npy", t)
x = t5[9000].copy(); x[0]=0; x[1]=2900*65536
t = traj(x, 20000)
for k in [0,100,200,500,1000,2000,4000,10000,20000]:
    r=t[k]; print(f"k {k} h {F(r[1]):.1f} vx {F(r[2]):.3f} vz {F(r[3]):.3f} rpm {F(r[7]):.0f} tmap {F(r[8]):.2f} eI {r[19]} ac {r[20]} q {r[6]}")
np.save("traj_above.npy", t)
