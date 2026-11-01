"""Reference-state table: actual escape loss vs required height under each envelope form."""
import math
import pandas as pd
from mu025 import H as H_mu025

ref = pd.read_csv('/tmp/envconf/ref_forms.csv')
cells = pd.read_csv('/tmp/envconf/cells.csv')
RHO, S, W, CLMAX, G = 1.112, 16.17, 853 * 9.80665, 1.47, 9.80665


def outer(V, g0):
    n = min(3.8, 0.5 * RHO * V * V * S * CLMAX / W)
    return 0.0 if g0 >= 0 else V * V / G * math.log((n - math.cos(g0)) / (n - 1))


rows = []
for V in (35, 45, 55):
    for g0 in (-0.3, -0.15, 0.0):
        r_idle = ref[(ref.V0.round(0) == V) & (ref.g0.round(2) == g0) & (ref.rpm0 < 1500)].iloc[0]
        r_full = ref[(ref.V0.round(0) == V) & (ref.g0.round(2) == g0) & (ref.rpm0 > 1500)].iloc[0]
        c = cells[(cells.V0 == V) & (cells.g0.round(2) == g0)].iloc[0]
        rows.append(dict(V=V, gam=g0, outer_approx=outer(V, g0), loss_idle=r_idle.loss, loss_full=r_full.loss,
                         loss_cell_worst=c.actual, H_C_cell=c.HC, H_B_cell=c.HB, H_C_oracle=r_idle.HC,
                         H_A_oracle=r_idle.HA, H_mu025=H_mu025(V, g0)))
t = pd.DataFrame(rows)
print(t.round(1).to_markdown(index=False))
