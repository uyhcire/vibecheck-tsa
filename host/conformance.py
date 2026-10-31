"""ABI conformance tests from docs/filter-interface.md section 6, run against libvcfilter through ctypes."""
import argparse
import ctypes as C
import json
import math
import os
import random
import subprocess
import sys
import tempfile
import threading

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vcfilter as vc  # noqa: E402

FAILS = []


def check(name, ok, detail=''):
    print(f'{"ok  " if ok else "FAIL"} {name}{": " + detail if detail else ""}')
    if not ok:
        FAILS.append(name)


def rss_kb():
    return int(subprocess.run(['ps', '-o', 'rss=', '-p', str(os.getpid())], capture_output=True, text=True).stdout)


def sequence(lib, seed, n):
    """Closed-loop synthetic (obs, pilot) ticks: random pilot, a plant inside P0's envelope, escapes climb."""
    rng = random.Random(seed)
    f = vc.Filter(lib)
    out = []
    for k in range(n):
        if k % 120 == 0:
            f.reset()
            x, h, vz, V = -400.0, rng.uniform(220, 400), 0.0, 52.0
        elev = rng.choice([0.0, 0.0, 0.0, -0.2, -0.1, rng.uniform(-1, 1)])
        pilot = vc.surfaces(elev, rng.random(), aileron=rng.uniform(-1, 1), rudder=rng.uniform(-1, 1),
                            brake=rng.random())
        pilot.nz, pilot.roll_rate = rng.uniform(-3, 3), rng.uniform(-1, 1)
        o = vc.obs(x, h, V, vz, V, t=k / 8)
        out.append((o, pilot))
        _, applied, _ = f.tick(o, pilot)
        if applied.kind == vc.CMD_ESCAPE:
            vz2, V2 = min(vz + 0.4, 4.5), V - 0.05
        else:
            vz2, V2 = vz + (rng.uniform(-0.2, 0.2) if elev <= 0 else -rng.uniform(0, 3)), V + rng.uniform(-0.05, 0.05)
        h += min(vz, vz2) / 8
        x += V / 8
        vz, V = vz2, V2
    f.close()
    return out


def record(f, seq):
    rows = []
    for o, p in seq:
        ret, a, i = f.tick(o, p)
        rows.append((ret, bytes(a), i.verdict, i.monitor_flags, i.margin, i.escape_id, i.tick_index, i.escape_phase,
                     i.escape_pull, i.escape_climb, i.escape_vmin))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--leak-ticks', type=int, default=1_000_000)
    a = ap.parse_args()
    lib = vc.load()
    f = vc.Filter(lib)
    seq = sequence(lib, 7, 3000)

    def sentinel():
        c = vc.Cmd()
        C.memset(C.byref(c), 0xAB, C.sizeof(c))
        return c
    good_o, good_p = vc.obs(-400, 300, 50, 0, 52), vc.surfaces(0.0, 0.6)
    nan_o, inf_o = vc.obs(-400, math.nan, 50, 0, 52), vc.obs(-400, 300, 50, 0, math.inf)
    nomask_o = vc.obs(-400, 300, 50, 0, 52, mask=vc.OBS_POS | vc.OBS_VEL)
    badver_o = vc.obs(-400, 300, 50, 0, 52)
    badver_o.abi_version = 99
    demand_p = vc.surfaces(0.0, 0.6)
    demand_p.kind = vc.CMD_DEMAND
    cases = [('valid', f.h, good_o, good_p, vc.OK), ('NaN field', f.h, nan_o, good_p, vc.ERR_BAD_OBS),
             ('inf field', f.h, inf_o, good_p, vc.ERR_BAD_OBS),
             ('missing airspeed', f.h, nomask_o, good_p, vc.ERR_BAD_OBS),
             ('NULL obs', f.h, None, good_p, vc.ERR_BAD_OBS), ('NULL pilot', f.h, good_o, None, vc.ERR_BAD_OBS),
             ('DEMAND pilot', f.h, good_o, demand_p, vc.ERR_BAD_OBS),
             ('bad obs version', f.h, badver_o, good_p, vc.ERR_BAD_OBS),
             ('NULL filter', None, good_o, good_p, vc.ERR_NOT_INIT)]
    for name, h, o, p, want in cases:
        f.reset()
        applied, info = sentinel(), vc.Info()
        ret = lib.vc_filter_tick(h, C.byref(o) if o else None, C.byref(p) if p else None, C.byref(applied),
                                 C.byref(info))
        written = applied.kind in (vc.CMD_SURFACES, vc.CMD_ESCAPE) and applied.abi_version == vc.ABI_VERSION
        safe = ret == vc.OK or (applied.kind == vc.CMD_ESCAPE and info.verdict == vc.MONITOR_FAIL and
                                info.monitor_flags & (1 << 8))
        check(f'applied written: {name}', ret == want and written and safe,
              f'ret {ret}, kind {applied.kind}, verdict {vc.VERDICTS.get(info.verdict)}')

    f.reset()
    r1 = record(f, seq)
    f.reset()
    r2 = record(f, seq)
    g = vc.Filter(lib)
    r3 = record(g, seq)
    g.close()
    check('determinism after reset', r1 == r2)
    check('determinism across handles', r1 == r3)
    verdicts = [r[2] for r in r1]
    print('     sequence verdicts: ' + ', '.join(f'{vc.VERDICTS[v]} {verdicts.count(v)}' for v in range(4)))

    f.reset()
    pass_ok, adm_ok, n_pass = True, True, 0
    for o, p in seq:
        ret, ap_, i = f.tick(o, p)
        if i.verdict == vc.PASS:
            n_pass += 1
            pass_ok &= bytes(ap_) == bytes(p)
        if ap_.kind == vc.CMD_ESCAPE:
            adm_ok &= (ap_.throttle, ap_.elevator, ap_.aileron, ap_.rudder, ap_.brake) == (1.0, 0.0, 0.0, 0.0, 0.0)
        else:
            adm_ok &= -1 <= ap_.elevator <= 1 and 0 <= ap_.throttle <= 1 and bytes(ap_) == bytes(p)
    check('passthrough on PASS (bitwise)', pass_ok and n_pass > 0, f'{n_pass} PASS ticks')
    check('admissible applied', adm_ok)

    f.reset()
    f.tick(vc.obs(0, 300, 50, 0, 55), vc.surfaces(0, 0.6))
    _, _, i1 = f.tick(vc.obs(7, 300, 64, 0, 55), vc.surfaces(0, 0.6))
    _, _, i2 = f.tick(vc.obs(13.5, 300, 50, 0, 55), vc.surfaces(0, 0.6))
    check('negative control: vx_max injected', i1.verdict == vc.MONITOR_FAIL and i1.monitor_flags == 2 | 2 << 16,
          f'flags {i1.monitor_flags:#x}')
    check('monitor flag latched until reset', i2.monitor_flags >> 16 & 2 and not i2.monitor_flags & 0xFFFF)
    f.reset()
    _, _, i3 = f.tick(vc.obs(0, 300, 50, 0, 55), vc.surfaces(0, 0.6))
    check('reset clears latch', i3.monitor_flags == 0 and i3.verdict == vc.PASS)

    threading.stack_size(16 << 20)
    results = {}

    def worker(name):
        h = vc.Filter(lib)
        results[name] = record(h, seq)
        h.close()
    ts = [threading.Thread(target=worker, args=(n,)) for n in ('a', 'b')]
    for t in ts:
        t.start()
    for t in ts:
        t.join()
    check('two handles, two threads, 16 MiB stacks', results.get('a') == r1 and results.get('b') == r1)

    f.reset()
    us = sorted(f.tick(o, p)[2].us_total for o, p in seq)
    p99 = us[int(0.99 * len(us))]
    check('timing p99 under 125 ms (8 Hz tick)', p99 < 125_000,
          f'us_total p50 {us[len(us) // 2]:.1f} p99 {p99:.1f} max {us[-1]:.1f}')

    gname = lib.vc_filter_guarantee(f.h).decode()
    audit = open(os.path.join(vc.ROOT, 'Tools', 'EnvelopeAudit.lean')).read()
    check('guarantee name is audited', gname.split('.')[-1] in audit, gname)

    def new(**kw):
        cfg = vc.Config(abi_version=kw.get('ver', vc.ABI_VERSION), size=C.sizeof(vc.Config),
                        kind=kw.get('kind', vc.FILTER_ENVELOPE), params_path=kw.get('path'))
        err = C.c_int(0)
        h = lib.vc_filter_new(C.byref(cfg), C.byref(err))
        if h:
            lib.vc_filter_free(h)
        return bool(h), err.value
    with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False) as bad:
        json.dump({'sag': -1}, bad)
    with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False) as good:
        json.dump({'margin': '25/2', 'terrain': {'cells': [0, 0, 100]}}, good)
    check('config: not WellFormed rejected', new(path=bad.name.encode()) == (False, vc.ERR_BAD_CONFIG))
    check('config: missing file rejected', new(path=b'/nonexistent.json') == (False, vc.ERR_BAD_CONFIG))
    check('config: JSON override accepted', new(path=good.name.encode()) == (True, vc.OK))
    check('config: wrong ABI version', new(ver=2) == (False, vc.ERR_VERSION))
    check('config: unsupported filter kind', new(kind=vc.FILTER_TUBE) == (False, vc.ERR_UNSUPPORTED))
    os.unlink(bad.name)
    os.unlink(good.name)

    for _ in range(20_000):
        f.tick(*seq[_ % len(seq)])
    base = rss_kb()
    for k in range(a.leak_ticks):
        if k % 400 == 0:
            f.reset()
        f.tick(*seq[k % len(seq)])
    mid = rss_kb()
    for _ in range(10_000):
        vc.Filter(lib).close()
    end = rss_kb()
    f.close()
    check(f'no leak over {a.leak_ticks} ticks', mid - base < 2048, f'RSS {base} -> {mid} KiB')
    check('no leak over 10^4 new/free', end - mid < 2048 and lib.vc_filter_live_objects() == 0,
          f'RSS {mid} -> {end} KiB, live handles {lib.vc_filter_live_objects()}')

    print(f'{len(FAILS)} failed' if FAILS else 'all passed')
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
