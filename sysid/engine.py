"""Can a small Lean-friendly engine model predict thrust one tick ahead? (RPM as a state.)"""
import csv, numpy as np
def load(p):
    rows = list(csv.DictReader(open(p)))
    A = np.array([[float(r[c]) for c in ['thr', 'rpm', 'vt', 'thrust']] for r in rows])
    ep = np.array([int(r['ep']) for r in rows]); ok = ep[:-1] == ep[1:]
    return A[:-1][ok], A[1:][ok]
def F(A):
    thr, rpm, vt = A[:, 0], A[:, 1] / 1000, A[:, 2] / 50
    return np.stack([np.ones_like(thr), thr, thr**2, rpm, rpm**2, rpm*vt, vt, vt**2, thr*rpm, thr*vt], 1)
(S, N), (T, U) = load('sysid/train.csv'), load('sysid/test.csv')
c_rpm, *_ = np.linalg.lstsq(F(S), N[:, 1] / 1000, rcond=None)          # rpm_{k+1}
c_thr, *_ = np.linalg.lstsq(F(N), N[:, 3], rcond=None)                 # thrust from (thr, rpm, V)
rpm_pred = F(T) @ c_rpm * 1000
U2 = U.copy(); U2[:, 1] = rpm_pred
thrust_pred = F(U2) @ c_thr
e = np.abs(thrust_pred - U[:, 3])
print(f'thrust one-tick error N: p50 {np.quantile(e,.5):.1f} p99 {np.quantile(e,.99):.1f} max {e.max():.1f}')
print(f'as velocity error per tick (m=1043 kg, dt=1/16): p99 {np.quantile(e,.99)/1043/16:.4f} max {e.max()/1043/16:.4f} m/s')
print('thrust range N', U[:, 3].min().round(), U[:, 3].max().round())
