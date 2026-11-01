import numpy as np, sample as sm
from sample import *
sm.GsN = np.load("GsN_fit.npy")
X = sm.sample(1000, 3.0, 0.0)
cur = X
for k in range(4):
    img, _, _ = ticks(cur)
    E = np.array([coords(xi)[2] for xi in img]); Yn = np.array([np.sqrt(V(*coords(xi)[:2])) for xi in img])
    print("tick", k+1, "fast resid max", np.abs(E).max(axis=0).round(2), " |y| max", Yn.max().round(3))
    cur = img
