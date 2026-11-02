"""Fine-tune the fly brain to fly the bandit: FlyGM (arXiv 2602.17997) on the pursuit subgraph from
build_graph.py, trained by imitation of combat::pursuit_law on rows written by `flybrain_data`.

Vision is a retina of the LC10s' receptive fields (retina.py): each LC10 gets its own response to the target
(in field, motion, size), computed from the row's sight (direction, its rate, log apparent radius) exactly as
`flybrain::retina` does. Proprioception goes through a small encoder to every LC10's gate.

The connectome's signed, input-normalised weights are fixed. Learned: per-neuron descriptors eta_v, the shared
neuron update MLP, the afferent gate, the proprioception encoder and the descending-neuron decoder.

usage: train.py OUT.bin DATA.f32 [DATA.f32 ...] [--init IN.bin] [--steps N] [--batch B]
"""

import struct
import sys
import time

import numpy as np
import torch
import torch.nn as nn

NOBS, NOWN, NR, NACT = 11, 4, 3, 4
C, HF, K, H_ENC, H_DEC = 16, 32, 4, 64, 64
RET_MOTION, LN_RHO0 = 0.3, -5.3

args = [a for a in sys.argv[1:]]
steps = 4000
if "--steps" in args:
    i = args.index("--steps")
    steps = int(args[i + 1])
    del args[i : i + 2]
B = 256
if "--batch" in args:
    i = args.index("--batch")
    B = int(args[i + 1])
    del args[i : i + 2]
init = None
if "--init" in args:
    i = args.index("--init")
    init = args[i + 1]
    del args[i : i + 2]
out_path, data_paths = args[0], args[1:]

dev = torch.device("cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu")
g = np.load("cache/graph.npz")
N, NA, NE = len(g["root_ids"]), int(g["n_aff"]), int(g["n_eff"])
W = torch.zeros(N, N)
W[torch.from_numpy(g["dst"].astype(np.int64)), torch.from_numpy(g["src"].astype(np.int64))] = torch.from_numpy(g["w"])

ret = np.load("cache/retina.npz")
RF_C, RF_S2 = torch.from_numpy(ret["c"]), torch.from_numpy(ret["s2"])
rows = np.concatenate([np.fromfile(p, dtype="<f4").reshape(-1, NOBS + NACT) for p in data_paths])
obs, act = rows[:, :NOBS], rows[:, NOBS:]
own_mean, own_std = obs[:, 7:].mean(0), obs[:, 7:].std(0) + 1e-3
act_mean, act_std = act.mean(0), act.std(0) + 1e-3
act_mean[3], act_std[3] = 0.0, 1.0  # fire is a logit
perm = np.random.default_rng(0).permutation(len(rows))
n_val = min(20000, len(rows) // 10)
val, tr = perm[:n_val], perm[n_val:]
X = torch.from_numpy(obs).float()
Y = torch.from_numpy((act - act_mean) / act_std).float()
print(f"{len(rows)} rows, graph {N} neurons ({NA} LC10, {NE} descending), {len(g['w'])} edges, device {dev}")


class FlyGM(nn.Module):
    def __init__(self):
        super().__init__()
        self.register_buffer("W", W)
        self.register_buffer("rf_c", RF_C)
        self.register_buffer("rf_s2", RF_S2)
        self.register_buffer("own_mean", torch.from_numpy(own_mean))
        self.register_buffer("own_std", torch.from_numpy(own_std))
        self.enc1, self.enc2 = nn.Linear(NOWN, H_ENC), nn.Linear(H_ENC, C)
        self.gate = nn.Linear(2 * C + NR, C)
        self.eta = nn.Parameter(0.5 * torch.randn(N, C))
        self.f1, self.f2 = nn.Linear(2 * C, HF), nn.Linear(HF, C)
        self.dec1, self.dec2 = nn.Linear(NE * C, H_DEC), nn.Linear(H_DEC, NACT)

    def retina(self, x):
        t, td, lr = x[:, 0:3], x[:, 3:6], x[:, 6:7]
        den = self.rf_s2[None] + torch.exp(2.0 * lr)
        r = torch.exp(-(1.0 - t @ self.rf_c.T) / den)
        motion = torch.tanh(r * (td @ self.rf_c.T) / den * RET_MOTION)
        return torch.stack([r, motion, r * (lr - LN_RHO0) * 0.5], -1)

    def forward(self, x):
        B = x.shape[0]
        ret = self.retina(x)
        xe = self.enc2(torch.tanh(self.enc1((x[:, 7:] - self.own_mean) / self.own_std)))
        H = x.new_zeros(B, N, C)
        eta = self.eta.expand(B, N, C)
        for _ in range(K):
            Ha = torch.tanh(self.gate(torch.cat([H[:, :NA], xe[:, None].expand(B, NA, C), ret], -1)))
            H = torch.cat([Ha, H[:, NA:]], 1)
            M = torch.einsum("vu,buc->bvc", self.W, H)
            H = torch.tanh(self.f2(torch.tanh(self.f1(torch.cat([M, eta], -1)))))
        return self.dec2(torch.tanh(self.dec1(H[:, N - NE :].reshape(B, -1))))


LAYERS = ["enc1", "enc2", "gate", "f1", "f2", "dec1", "dec2"]


def export(m, path):
    sd = {k: v.detach().cpu().numpy().astype("<f4") for k, v in m.state_dict().items()}
    with open(path, "wb") as f:
        f.write(b"FLYB")
        f.write(struct.pack("<13I", 2, N, NA, NE, C, K, NOBS, NOWN, NACT, H_ENC, HF, H_DEC, len(g["w"])))
        arrays = [own_mean, own_std]
        for name in ["enc1", "enc2", "gate"]:
            arrays += [sd[name + ".weight"], sd[name + ".bias"]]
        arrays.append(sd["eta"])
        for name in ["f1", "f2", "dec1", "dec2"]:
            arrays += [sd[name + ".weight"], sd[name + ".bias"]]
        arrays += [act_mean, act_std, ret["c"], ret["s2"]]
        for a in arrays:
            f.write(np.ascontiguousarray(a, dtype="<f4").tobytes())
        f.write(g["src"].astype("<u4").tobytes())
        f.write(g["dst"].astype("<u4").tobytes())
        f.write(g["w"].astype("<f4").tobytes())


def load(m, path):
    """Warm start from an earlier export (same graph and sizes)."""
    b = open(path, "rb").read()
    o = 4 + 4 * 13
    def take(shape):
        nonlocal o
        n = int(np.prod(shape))
        a = np.frombuffer(b, "<f4", n, o).reshape(shape)
        o += 4 * n
        return torch.from_numpy(a.copy())
    take((NOWN,)), take((NOWN,))
    sd = m.state_dict()
    shapes = {k: v.shape for k, v in sd.items()}
    for name in ["enc1", "enc2", "gate"]:
        sd[name + ".weight"], sd[name + ".bias"] = take(shapes[name + ".weight"]), take(shapes[name + ".bias"])
    sd["eta"] = take(shapes["eta"])
    for name in ["f1", "f2", "dec1", "dec2"]:
        sd[name + ".weight"], sd[name + ".bias"] = take(shapes[name + ".weight"]), take(shapes[name + ".bias"])
    m.load_state_dict(sd)


model = FlyGM().to(dev)
if init:
    load(model, init)
opt = torch.optim.AdamW(model.parameters(), lr=1e-3 if not init else 3e-4, weight_decay=1e-4)
sched = torch.optim.lr_scheduler.OneCycleLR(opt, max_lr=opt.param_groups[0]["lr"], total_steps=steps, pct_start=0.05)
w_act = torch.tensor([1.0, 1.0, 0.5], device=dev)
bce = nn.BCEWithLogitsLoss(pos_weight=torch.tensor(3.0, device=dev))


def loss_fn(pred, y):
    mse = ((pred[:, :3] - y[:, :3]) ** 2 * w_act).mean()
    return mse + 0.5 * bce(pred[:, 3], y[:, 3]), mse


Xv, Yv = X[val].to(dev), Y[val].to(dev)
t0 = time.time()
rng = np.random.default_rng(1)
for step in range(1, steps + 1):
    idx = tr[rng.integers(0, len(tr), B)]
    xb, yb = X[idx].to(dev), Y[idx].to(dev)
    loss, _ = loss_fn(model(xb), yb)
    opt.zero_grad()
    loss.backward()
    nn.utils.clip_grad_norm_(model.parameters(), 1.0)
    opt.step()
    sched.step()
    if step % 500 == 0 or step == steps:
        with torch.no_grad():
            pv = torch.cat([model(Xv[i : i + 1000]) for i in range(0, len(Xv), 1000)])
            vl, vmse = loss_fn(pv, Yv)
            fire_acc = ((pv[:, 3] > 0) == (Yv[:, 3] > 0.5)).float().mean().item()
            pos = Yv[:, 3] > 0.5
            fire_rec = (pv[pos, 3] > 0).float().mean().item()
            fire_prec = (Yv[pv[:, 3] > 0, 3] > 0.5).float().mean().item()
            bank_err = ((pv[:, 0] - Yv[:, 0]).abs().mean() * act_std[0]).item()
        print(f"step {step}: train {loss.item():.4f} val {vl.item():.4f} (mse {vmse.item():.4f}) bank err {np.degrees(bank_err):.1f} deg, fire acc {fire_acc:.3f} (recall {fire_rec:.2f}, precision {fire_prec:.2f})  {time.time() - t0:.0f} s", flush=True)
        export(model, out_path)
print("wrote", out_path)
