"""Cut the fly's visual pursuit pathway out of the FlyWire v783 connectome.

Afferents: every LC10 neuron (lobula columnar type 10, the visual projection neurons male flies use to track and
chase a target). Efferents: the descending neurons that get the most input from the rest of the subgraph.
Intrinsic: the central-brain neurons that sit on the strongest LC10 -> descending paths (forward reach from LC10
times backward reach from the descending neurons, three hops each way). Edges are every connection of at least
5 synapses among them, signed by the presynaptic neuron's neurotransmitter (Shiu et al. 2024's table) and divided
by the target's total input, as FlyGM's message passing expects.

Writes cache/graph.npz: nodes ordered afferents, intrinsic, efferents; edges as (src, dst, w).
"""

import numpy as np
import pandas as pd

N_INTRINSIC = 1500
N_EFFERENT = 256
MIN_SYN = 5

conn = pd.read_parquet("cache/Connectivity_783.parquet")
conn = conn[conn.Connectivity >= MIN_SYN]
ann = pd.read_csv("cache/annotations.tsv", sep="\t", low_memory=False, usecols=["root_id", "super_class", "cell_type"])
ids = pd.read_csv("cache/Completeness_783.csv", index_col=0).index.to_numpy()
n_all = len(ids)
ann = ann.set_index("root_id").reindex(ids)
sc = ann.super_class.fillna("").to_numpy()
ct = ann.cell_type.fillna("").to_numpy()

pre = conn.Presynaptic_Index.to_numpy()
post = conn.Postsynaptic_Index.to_numpy()
cnt = conn.Connectivity.to_numpy().astype(np.float64)
signed = conn["Excitatory x Connectivity"].to_numpy().astype(np.float64)

aff = np.flatnonzero(np.char.startswith(ct.astype(str), "LC10"))
dns = np.flatnonzero(sc == "descending")
central = sc == "central"

out_deg = np.bincount(pre, weights=cnt, minlength=n_all)
in_deg = np.bincount(post, weights=cnt, minlength=n_all)
w_fwd = cnt / np.maximum(out_deg[pre], 1.0)
w_bwd = cnt / np.maximum(in_deg[post], 1.0)


def reach(seed, forward, hops=3):
    r = np.zeros(n_all)
    r[seed] = 1.0
    total = np.zeros(n_all)
    for _ in range(hops):
        if forward:
            r = np.bincount(post, weights=w_fwd * r[pre], minlength=n_all)
        else:
            r = np.bincount(pre, weights=w_bwd * r[post], minlength=n_all)
        total += r
    return total


score = reach(aff, True) * reach(dns, False)
score[~central] = 0.0
intr = np.argsort(-score)[:N_INTRINSIC]
intr = intr[score[intr] > 0]

# Descending neurons ranked by synapses from the afferents and intrinsic neurons.
src_set = np.zeros(n_all, bool)
src_set[aff] = True
src_set[intr] = True
dn_in = np.bincount(post, weights=cnt * src_set[pre], minlength=n_all)
eff = dns[np.argsort(-dn_in[dns])[:N_EFFERENT]]
eff = eff[dn_in[eff] > 0]

nodes = np.concatenate([aff, intr, eff])
local = -np.ones(n_all, np.int64)
local[nodes] = np.arange(len(nodes))
keep = (local[pre] >= 0) & (local[post] >= 0)
src, dst, w = local[pre[keep]], local[post[keep]], signed[keep]
tot = np.bincount(dst, weights=np.abs(w), minlength=len(nodes))
w = w / np.maximum(tot[dst], 1.0)

np.savez(
    "cache/graph.npz",
    root_ids=ids[nodes],
    cell_types=ct[nodes],
    n_aff=len(aff),
    n_eff=len(eff),
    src=src.astype(np.uint32),
    dst=dst.astype(np.uint32),
    w=w.astype(np.float32),
)
types = pd.Series(ct[intr]).value_counts()
print(f"neurons {len(nodes)}: {len(aff)} LC10 afferents, {len(intr)} intrinsic, {len(eff)} descending; edges {len(w)}")
print("top intrinsic types:", types.head(8).to_dict())
print("efferents include:", sorted(set(ct[eff]) & {"DNa02", "DNa01", "DNb05", "DNp03", "DNg02", "DNa04", "DNp15", "DNb01"}))
