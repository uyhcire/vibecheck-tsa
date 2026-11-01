"""ctypes binding for the safety-filter C ABI (c/vcfilter.h), loading .lake/build/lib/libvcfilter.dylib."""
import ctypes as C
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIB_PATH = os.path.join(ROOT, '.lake', 'build', 'lib', 'libvcfilter.dylib')

ABI_VERSION = 1
FILTER_ENVELOPE, FILTER_TUBE, FILTER_ROLLOUT = 1, 2, 3
OK, ERR_BAD_OBS, ERR_NOT_INIT, ERR_INTERNAL, ERR_BAD_CONFIG, ERR_VERSION, ERR_UNSUPPORTED = 0, -1, -2, -3, -4, -5, -6
PASS, ADJUSTED, ESCAPE, MONITOR_FAIL = 0, 1, 2, 3
VERDICTS = {PASS: 'PASS', ADJUSTED: 'ADJUSTED', ESCAPE: 'ESCAPE', MONITOR_FAIL: 'MONITOR_FAIL'}
CMD_SURFACES, CMD_DEMAND, CMD_ESCAPE = 1, 2, 3
OBS_T, OBS_POS, OBS_VEL, OBS_ATT, OBS_RATES, OBS_ELEV, OBS_THROTTLE, OBS_FUEL, OBS_GROUND, OBS_AIRSPEED = (
    1 << i for i in range(10))
MON_BITS = ['vx_min', 'vx_max', 'x_lo', 'x_hi', 'h_gain', 'vz_floor', 'v_floor', 'init', 'bad_obs', 'substep']
LATCH_SHIFT = 16


class Config(C.Structure):
    _fields_ = [('abi_version', C.c_uint32), ('size', C.c_uint32), ('kind', C.c_uint32), ('reserved', C.c_uint32),
                ('seed', C.c_uint64), ('params_path', C.c_char_p)]


class Obs(C.Structure):
    _fields_ = [('abi_version', C.c_uint32), ('size', C.c_uint32), ('t', C.c_double), ('pos', C.c_double * 3),
                ('vel', C.c_double * 3), ('pitch', C.c_double), ('roll', C.c_double), ('yaw', C.c_double),
                ('rates', C.c_double * 3), ('elev_pos', C.c_double), ('throttle_pos', C.c_double),
                ('fuel', C.c_double), ('on_ground', C.c_uint32), ('valid_mask', C.c_uint32),
                ('airspeed', C.c_double)]


class Cmd(C.Structure):
    _fields_ = [('abi_version', C.c_uint32), ('size', C.c_uint32), ('kind', C.c_uint32), ('reserved', C.c_uint32),
                ('elevator', C.c_double), ('aileron', C.c_double), ('rudder', C.c_double), ('throttle', C.c_double),
                ('brake', C.c_double), ('nz', C.c_double), ('roll_rate', C.c_double)]


class Info(C.Structure):
    _fields_ = [('abi_version', C.c_uint32), ('size', C.c_uint32), ('verdict', C.c_int32),
                ('monitor_flags', C.c_uint32), ('margin', C.c_double), ('escape_id', C.c_uint64),
                ('tick_index', C.c_uint64), ('us_total', C.c_double), ('us_lean', C.c_double),
                ('escape_phase', C.c_uint32), ('reserved', C.c_uint32), ('escape_pull', C.c_double),
                ('escape_climb', C.c_double), ('escape_vmin', C.c_double)]


def load(path=LIB_PATH):
    lib = C.CDLL(path)
    lib.vc_filter_new.restype = C.c_void_p
    lib.vc_filter_new.argtypes = [C.POINTER(Config), C.POINTER(C.c_int)]
    lib.vc_filter_tick.restype = C.c_int
    lib.vc_filter_tick.argtypes = [C.c_void_p, C.POINTER(Obs), C.POINTER(Cmd), C.POINTER(Cmd), C.POINTER(Info)]
    lib.vc_filter_tick_substeps.restype = C.c_int
    lib.vc_filter_tick_substeps.argtypes = [C.c_void_p, C.POINTER(Obs), C.POINTER(Cmd), C.POINTER(Cmd),
                                            C.POINTER(Info), C.POINTER(Obs), C.c_uint32]
    lib.vc_filter_reset.argtypes = [C.c_void_p]
    lib.vc_filter_free.argtypes = [C.c_void_p]
    lib.vc_filter_guarantee.restype = C.c_char_p
    lib.vc_filter_guarantee.argtypes = [C.c_void_p]
    lib.vc_filter_command_kind.restype = C.c_uint32
    lib.vc_filter_command_kind.argtypes = [C.c_void_p]
    lib.vc_filter_required_obs.restype = C.c_uint32
    lib.vc_filter_required_obs.argtypes = [C.c_void_p]
    lib.vc_filter_live_handles.restype = C.c_int64
    return lib


def obs(x, h, vx, vz, V, t=0.0, mask=OBS_POS | OBS_VEL | OBS_AIRSPEED):
    o = Obs(abi_version=ABI_VERSION, size=C.sizeof(Obs), t=t, valid_mask=mask, airspeed=V)
    o.pos[0], o.pos[2], o.vel[0], o.vel[2] = x, h, vx, vz
    return o


def surfaces(elevator, throttle, aileron=0.0, rudder=0.0, brake=0.0):
    return Cmd(abi_version=ABI_VERSION, size=C.sizeof(Cmd), kind=CMD_SURFACES, elevator=elevator,
               aileron=aileron, rudder=rudder, throttle=throttle, brake=brake)


def flag_names(bits):
    return [n for i, n in enumerate(MON_BITS) if bits >> i & 1]


class Filter:
    """One filter handle; `tick` returns (ret, applied, info)."""

    def __init__(self, lib, params_path=None, kind=FILTER_ENVELOPE):
        self.lib = lib
        cfg = Config(abi_version=ABI_VERSION, size=C.sizeof(Config), kind=kind,
                     params_path=params_path.encode() if params_path else None)
        err = C.c_int(0)
        self.h = lib.vc_filter_new(C.byref(cfg), C.byref(err))
        self.err = err.value
        if not self.h:
            raise RuntimeError(f'vc_filter_new failed: {err.value}')

    def tick(self, o, pilot, subs=()):
        applied, info = Cmd(), Info()
        arr = (Obs * len(subs))(*subs) if subs else None
        ret = self.lib.vc_filter_tick_substeps(self.h, C.byref(o) if o is not None else None,
                                               C.byref(pilot) if pilot is not None else None, C.byref(applied),
                                               C.byref(info), arr, len(subs))
        return ret, applied, info

    def reset(self):
        self.lib.vc_filter_reset(self.h)

    def close(self):
        if self.h:
            self.lib.vc_filter_free(self.h)
            self.h = None
