"""Front-view layout of the fly brain's neurons for the GUI's firing panel.

Each neuron sits at its FlyWire position (a point on its arbor, `pos_x`/`pos_y` in 4 nm voxels, converted to µm;
y grows ventrally). Also picks the strongest connections to draw as wiring: up to 400 each of LC10 -> central,
central -> central and central -> descending, by absolute input-normalised weight.

Writes ../assets/flybrain_layout.bin: b"FLYL", u32 N, N x (f32 x, f32 y), u32 M, M x (u32 src, u32 dst, f32 w).
"""

import struct

import numpy as np
import pandas as pd

g = np.load("cache/graph.npz", allow_pickle=True)
ids = g["root_ids"]
n, na, ne = len(ids), int(g["n_aff"]), int(g["n_eff"])
a = pd.read_csv("cache/annotations.tsv", sep="\t", low_memory=False, usecols=["root_id", "pos_x", "pos_y"])
a = a.drop_duplicates("root_id").set_index("root_id").reindex(ids)
xy = np.stack([a.pos_x.to_numpy() * 4e-3, a.pos_y.to_numpy() * 4e-3], 1).astype("<f4")

src, dst, w = g["src"].astype(np.int64), g["dst"].astype(np.int64), g["w"]
cls = np.where(np.arange(n) < na, 0, np.where(np.arange(n) >= n - ne, 2, 1))
picks = []
for cs, cd in [(0, 1), (1, 1), (1, 2)]:
    idx = np.flatnonzero((cls[src] == cs) & (cls[dst] == cd))
    picks.append(idx[np.argsort(-np.abs(w[idx]))[:400]])
e = np.concatenate(picks)

with open("../assets/flybrain_layout.bin", "wb") as f:
    f.write(b"FLYL")
    f.write(struct.pack("<I", n))
    f.write(xy.tobytes())
    f.write(struct.pack("<I", len(e)))
    for i in e:
        f.write(struct.pack("<IIf", src[i], dst[i], w[i]))
print(f"{n} neurons, {len(e)} edges; x {xy[:, 0].min():.0f}-{xy[:, 0].max():.0f} µm, y {xy[:, 1].min():.0f}-{xy[:, 1].max():.0f} µm")
