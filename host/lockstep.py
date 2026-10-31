"""JSBSim c172p in lockstep with the envelope filter over the filter's terrain grid, taken as the true terrain."""
import argparse
import csv
import json
import math
import random
import statistics
import sys
import os

import jsbsim

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vcfilter as vc  # noqa: E402

FT = 0.3048
SUB = 16                 # JSBSim steps (1/128 s) per filter tick (P0.dt = 1/8 s)
TICKS = 480              # 60 s per episode
ELEV_RATE = 2.0 / 128    # actuator rate limit per JSBSim step (2/s)

P0_TERRAIN = dict(x0=0.0, w=50.0, beyond=0.0, cells=[0] * 6 + [200] * 10 + [0] * 4)


def rat(v):
    if isinstance(v, str):
        p, _, q = v.partition('/')
        return float(p) / float(q or 1)
    return float(v)


def load_terrain(path):
    t = dict(P0_TERRAIN)
    if path:
        t.update(json.load(open(path)).get('terrain', {}))
    return dict(x0=rat(t['x0']), w=rat(t['w']), beyond=rat(t['beyond']), cells=[rat(c) for c in t['cells']])


def height_at(T, x):
    i = math.floor((x - T['x0']) / T['w'])
    return T['cells'][i] if 0 <= i < len(T['cells']) else T['beyond']


def make_fdm(rng):
    fdm = jsbsim.FGFDMExec(None)
    fdm.set_debug_level(0)
    fdm.load_model('c172p')
    fdm['ic/h-sl-ft'] = rng.uniform(280, 380) / FT
    fdm['ic/terrain-elevation-ft'] = 0
    fdm['ic/vc-kts'] = rng.uniform(90, 105)
    fdm['ic/gamma-deg'] = 0
    fdm['ic/psi-true-deg'] = 90
    fdm.set_dt(1 / 128)
    fdm.run_ic()
    fdm['propulsion/set-running'] = -1
    fdm['fcs/mixture-cmd-norm'] = 0.9
    fdm['fcs/throttle-cmd-norm'] = 0.7
    fdm['simulation/do_simple_trim'] = 1
    return fdm


def leveler(fdm):
    """Lateral autopilot for every pilot: hold heading east (the filter's x axis) with small bank angles."""
    phi, p, r = fdm['attitude/phi-rad'], fdm['velocities/p-rad_sec'], fdm['velocities/r-rad_sec']
    dpsi = (fdm['attitude/psi-rad'] - math.pi / 2 + math.pi) % (2 * math.pi) - math.pi
    phi_t = max(-0.15, min(0.15, -0.8 * dpsi - 1.0 * r))
    fdm['fcs/aileron-cmd-norm'] = max(-1, min(1, -8.0 * (phi - phi_t) - 2.0 * p))
    fdm['fcs/rudder-cmd-norm'] = 0.0  # centred rudder keeps sideslip near 0 (sysid/collect.py rud0)


def escape_elevator(fdm):
    """Escape autopilot: pitch attitude target from airspeed (pull, then hold ~45 m/s in the climb); + is nose down."""
    V = fdm['velocities/vt-fps'] * FT
    theta, q = fdm['attitude/theta-rad'], fdm['velocities/q-rad_sec']
    target = max(0.0, min(0.30, 0.17 + 0.03 * (V - 45.0)))
    return max(-1.0, min(1.0, 2.0 * (theta - target) + 0.8 * q))


def pilot(rng, kind):
    """Yields (elevator, throttle) per tick; `dive` waits for a trigger point then pushes at the terrain."""
    k = 0
    trigger = rng.randint(0, 200)
    while True:
        if kind == 'dive' and k < trigger:
            hold, elev, thr = 1, 0.0, 0.7
        else:
            hold = rng.randint(8, 32)
            elev = rng.uniform(0.2, 1.0) if kind == 'dive' else rng.uniform(-0.5, 1.0)
            thr = rng.choice([0.0, 1.0, rng.random()])
        for _ in range(hold):
            k += 1
            yield elev, thr


def observe(fdm, x, t):
    ve = fdm['velocities/v-east-fps'] * FT
    return vc.obs(x, fdm['position/h-sl-meters'], ve, -fdm['velocities/v-down-fps'] * FT,
                  fdm['velocities/vt-fps'] * FT, t=t)


def episode(ep, seed, filt, T, log):
    rng = random.Random(seed * 100003 + ep)
    fdm = make_fdm(rng)
    kind = 'dive' if ep % 2 else 'random'
    x = rng.uniform(-800, -300)
    gen = pilot(rng, kind)
    elev_act = 0.0
    res = dict(ep=ep, kind=kind, crashed=False, crash_x=None, min_clear=math.inf, verdicts=[0, 0, 0, 0],
               mon_ticks=0, clause_counts=[0] * len(vc.MON_BITS), first_fail=None, us_lean=[], us_total=[],
               margins=[], escaped_at=None, ticks=0, diverged=False)
    if filt:
        filt.reset()
    for k in range(TICKS):
        p_elev, p_thr = next(gen)
        pilot_cmd = vc.surfaces(p_elev, p_thr)
        o = observe(fdm, x, k / 8)
        if filt:
            ret, applied, info = filt.tick(o, pilot_cmd)
            res['verdicts'][info.verdict] += 1
            res['us_lean'].append(info.us_lean)
            res['us_total'].append(info.us_total)
            res['margins'].append(info.margin)
            now = info.monitor_flags & 0xFFFF
            if info.verdict == vc.MONITOR_FAIL:
                res['mon_ticks'] += 1
                if res['first_fail'] is None:
                    res['first_fail'] = (k, vc.flag_names(now))
            for i in range(len(vc.MON_BITS)):
                res['clause_counts'][i] += now >> i & 1
            if applied.kind == vc.CMD_ESCAPE and res['escaped_at'] is None:
                res['escaped_at'] = k
        else:
            applied, info, ret = pilot_cmd, None, 0
        if log is not None:
            log.writerow(dict(ep=ep, k=k, x=x, h=o.pos[2], vx=o.vel[0], vz=o.vel[2], V=o.airspeed,
                              terrain=height_at(T, x), pilot_elev=p_elev, pilot_thr=p_thr, applied_kind=applied.kind,
                              verdict=vc.VERDICTS[info.verdict] if info else '', flags=info.monitor_flags if info else 0,
                              margin=info.margin if info else '', us_lean=info.us_lean if info else '',
                              phase=info.escape_phase if info else ''))
        escaping = applied.kind == vc.CMD_ESCAPE
        fdm['fcs/throttle-cmd-norm'] = 1.0 if escaping else applied.throttle
        for _ in range(SUB):
            target = escape_elevator(fdm) if escaping else applied.elevator
            elev_act += max(-ELEV_RATE, min(ELEV_RATE, target - elev_act))
            fdm['fcs/elevator-cmd-norm'] = elev_act
            leveler(fdm)
            fdm.run()
            x += fdm['velocities/v-east-fps'] * FT / 128
            if not math.isfinite(x + fdm['position/h-sl-meters']):
                res['crashed'], res['crash_x'], res['ticks'], res['diverged'] = True, math.nan, k + 1, True
                return res
            clear = fdm['position/h-sl-meters'] - height_at(T, x)
            res['min_clear'] = min(res['min_clear'], clear)
            if clear <= 0:
                res['crashed'], res['crash_x'], res['ticks'] = True, x, k + 1
                return res
        res['ticks'] = k + 1
    return res


def pct(xs, p):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(p / 100 * len(xs)))] if xs else float('nan')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--episodes', type=int, default=100)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--params')
    ap.add_argument('--csv')
    a = ap.parse_args()
    T = load_terrain(a.params)
    lib = vc.load()
    filt = vc.Filter(lib, a.params)
    print(f'guarantee: {lib.vc_filter_guarantee(filt.h).decode()}  params: {a.params or "P0"}  episodes: {a.episodes}')
    out = open(a.csv, 'w', newline='') if a.csv else None
    log = csv.DictWriter(out, ['ep', 'k', 'x', 'h', 'vx', 'vz', 'V', 'terrain', 'pilot_elev', 'pilot_thr',
                               'applied_kind', 'verdict', 'flags', 'margin', 'us_lean', 'phase']) if out else None
    if log:
        log.writeheader()
    raw = [episode(ep, a.seed, None, T, None) for ep in range(a.episodes)]
    fil = [episode(ep, a.seed, filt, T, log) for ep in range(a.episodes)]
    filt.close()
    if out:
        out.close()
    for name, rs in (('no filter', raw), ('filter', fil)):
        crashes = [r for r in rs if r['crashed']]
        by_kind = {k: sum(r['crashed'] for r in rs if r['kind'] == k) for k in ('random', 'dive')}
        print(f'{name:9s}: crashes {len(crashes)}/{len(rs)} (random pilot {by_kind["random"]}, dive pilot '
              f'{by_kind["dive"]}, JSBSim diverged {sum(r["diverged"] for r in rs)}); min clearance over all episodes {min(r["min_clear"] for r in rs):.1f} m')
    ticks = sum(r['ticks'] for r in fil)
    v = [sum(r['verdicts'][i] for r in fil) for i in range(4)]
    print(f'filter ticks {ticks}: ' + ', '.join(f'{vc.VERDICTS[i]} {v[i]}' for i in range(4)))
    print(f'episodes escaped: {sum(r["escaped_at"] is not None for r in fil)}; '
          f'episodes with a monitor fail: {sum(r["mon_ticks"] > 0 for r in fil)}; monitor-fail ticks: '
          f'{sum(r["mon_ticks"] for r in fil)}')
    cc = [sum(r['clause_counts'][i] for r in fil) for i in range(len(vc.MON_BITS))]
    print('failed clause counts (ticks): ' + ', '.join(f'{n} {c}' for n, c in zip(vc.MON_BITS, cc) if c))
    firsts = {}
    for r in fil:
        if r['first_fail']:
            key = '+'.join(r['first_fail'][1])
            firsts[key] = firsts.get(key, 0) + 1
    print('first failing clause per episode: ' + ', '.join(f'{k} {n}' for k, n in sorted(firsts.items())))
    first_k = [r['first_fail'][0] for r in fil if r['first_fail']]
    if first_k:
        print(f'first monitor fail at tick: median {statistics.median(first_k)}, min {min(first_k)}')
    ul = [u for r in fil for u in r['us_lean']]
    ut = [u for r in fil for u in r['us_total']]
    print(f'us_lean  p50 {pct(ul, 50):.1f}  p99 {pct(ul, 99):.1f}  max {max(ul):.1f}')
    print(f'us_total p50 {pct(ut, 50):.1f}  p99 {pct(ut, 99):.1f}  max {max(ut):.1f}')
    m = [x for r in fil for x in r['margins']]
    print(f'margin (m) p1 {pct(m, 1):.1f}  p50 {pct(m, 50):.1f}  max {max(m):.1f}')
    for r in fil:
        if r['crashed']:
            print(f'  filtered crash: ep {r["ep"]} ({r["kind"]}) at x={r["crash_x"]:.0f} tick {r["ticks"]}, '
                  f'escaped at {r["escaped_at"]}, first monitor fail {r["first_fail"]}')


if __name__ == '__main__':
    main()
