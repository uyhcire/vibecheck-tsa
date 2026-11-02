"""Receptive fields for the fly brain's LC10 neurons, from where each one sits in the optic lobe.

Each compound eye projects to the optic lobe on its own side, so left-lobe LC10s see the left eye's field (azimuth
> 0 is left in the body frame) and right-lobe ones the right. Within a lobe, a neuron's rank along the
anterior-posterior axis (pos_z) sets its azimuth, from 10 deg across the midline (binocular overlap) out to 165
deg, and its rank along the dorsal-ventral axis (pos_y) its elevation, -75..75 deg. Both are warped toward the
front, like a fly's acute zone, and fields widen with eccentricity: sigma = 2 deg + 0.1 x eccentricity.

Writes cache/retina.npz: c (n_aff x 3 unit vectors, body frame x forward, y left, z up) and s2 (sigma^2, rad^2),
in the graph's afferent order.
"""

import numpy as np
import pandas as pd

g = np.load("cache/graph.npz", allow_pickle=True)
na = int(g["n_aff"])
ids = g["root_ids"][:na]
a = pd.read_csv("cache/annotations.tsv", sep="\t", low_memory=False, usecols=["root_id", "side", "pos_y", "pos_z"])
a = a.drop_duplicates("root_id").set_index("root_id").reindex(ids)
side = np.where(a.side.to_numpy() == "left", 1.0, -1.0)


def rank01(x):
    r = np.empty(len(x))
    r[np.argsort(x, kind="stable")] = np.arange(len(x))
    return (r + 0.5) / len(x)


u_az, u_el = np.zeros(na), np.zeros(na)
for s in (1.0, -1.0):
    m = side == s
    u_az[m] = rank01(a.pos_z.to_numpy()[m])
    u_el[m] = 1.0 - rank01(a.pos_y.to_numpy()[m])  # pos_y grows ventrally
az = np.radians(side * (-10.0 + 175.0 * u_az**1.8))
w = 2.0 * u_el - 1.0
el = np.radians(75.0 * np.sign(w) * np.abs(w) ** 1.6)
c = np.stack([np.cos(el) * np.cos(az), np.cos(el) * np.sin(az), np.sin(el)], 1).astype("<f4")
ecc = np.degrees(np.arccos(np.clip(c[:, 0], -1, 1)))
sigma = np.radians(2.0 + 0.1 * ecc)
np.savez("cache/retina.npz", c=c, s2=(sigma**2).astype("<f4"))
print(f"{na} LC10: {int((side > 0).sum())} left, {int((side < 0).sum())} right; within 5 deg of the nose: {(ecc < 5).sum()}, 15 deg: {(ecc < 15).sum()}, 45 deg: {(ecc < 45).sum()}")
