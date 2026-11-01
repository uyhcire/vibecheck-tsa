import numpy as np
from pf import *
Mall = np.load("man2.npy"); hs = Mall[:,1]/65536
HT = np.arange(0, 2660, 10)
starts = []
for h in HT:
    x = Mall[np.argmin(abs(hs - max(h, 6)))].copy(); x[0] = 0; x[1] = int(h * 65536); starts.append(x)
E = frozen(np.array(starts), 3000)
E2 = frozen(E, 200)
print("max change over 200 more ticks per field:", np.abs(E2 - E).max(axis=0))
np.save("frozen.npy", E)
for k in range(0, len(HT), 30): print(HT[k], E[k,2]/65536, E[k,3]/65536, E[k,7]/65536, E[k,19])
