"""Map frame shared by fetch.py and build.py.

The world frame is UTM zone 10N (WGS84) easting/northing minus the origin's,
in metres: x east, y north (grid north, 0.37 deg from true north here).
Heights are NAVD88 metres, the datum of both DataSF and USGS 3DEP. UTM's
scale factor here is 0.99963, so map distances are 0.04% short of ground
distances; irrelevant for flight.
"""

import math

# Kearny & Market, roughly. The flyable rectangle (map metres, must match the
# bounds in sf_world.bin) runs from Ocean Beach and Lands End to Yerba Buena
# Island, and from Noe Valley and Twin Peaks to the Golden Gate's north
# anchorage. Edges are multiples of 200 m so every grid divides it evenly.
ORIGIN_LON = -122.4050
ORIGIN_LAT = 37.7910
X0, X1 = -9600.0, 3000.0
Y0, Y1 = -5000.0, 4400.0
FETCH_MARGIN = 150.0

# The Golden Gate Bridge: south tower centre, unit vector to the north tower,
# and the corridor (along the axis from the south tower, half-width across)
# that world.rs fills with the bridge itself. OSM's parts of it are skipped.
GG_S = (-6432.1, 2515.1)
GG_U = (-0.09788, 0.99520)
GG_CORRIDOR = (-700.0, 1700.0, 60.0)

_A = 6378137.0
_F = 1 / 298.257223563
_K0 = 0.9996
_LON0 = math.radians(-123.0)  # zone 10 central meridian
_N = _F / (2 - _F)
_AA = _A / (1 + _N) * (1 + _N**2 / 4 + _N**4 / 64)
_ALPHA = (
    _N / 2 - 2 * _N**2 / 3 + 5 * _N**3 / 16,
    13 * _N**2 / 48 - 3 * _N**3 / 5,
    61 * _N**3 / 240,
)
_C = 2 * math.sqrt(_N) / (1 + _N)


def utm_forward(lon, lat):
    """WGS84 lon/lat (degrees) to UTM 10N (easting, northing), Krüger series
    to third order in n (sub-millimetre inside the zone)."""
    phi = math.radians(lat)
    dl = math.radians(lon) - _LON0
    t = math.sinh(math.atanh(math.sin(phi)) - _C * math.atanh(_C * math.sin(phi)))
    xi = math.atan2(t, math.cos(dl))
    eta = math.atanh(math.sin(dl) / math.sqrt(1 + t * t))
    e = eta + sum(a * math.cos(2 * j * xi) * math.sinh(2 * j * eta) for j, a in enumerate(_ALPHA, 1))
    n = xi + sum(a * math.sin(2 * j * xi) * math.cosh(2 * j * eta) for j, a in enumerate(_ALPHA, 1))
    return 500000.0 + _K0 * _AA * e, _K0 * _AA * n


_E0, _N0 = utm_forward(ORIGIN_LON, ORIGIN_LAT)


def to_local(lon, lat):
    e, n = utm_forward(lon, lat)
    return e - _E0, n - _N0


def lonlat_bbox(margin):
    """A lon/lat box (w, s, e, n) that contains the flyable rectangle grown by
    `margin` (padded 10%: the UTM grid is slightly rotated against lon/lat)."""
    pad = 1.10
    k = 111_320.0 * math.cos(math.radians(ORIGIN_LAT))
    return (
        ORIGIN_LON + (X0 - margin) * pad / k,
        ORIGIN_LAT + (Y0 - margin) * pad / 111_000.0,
        ORIGIN_LON + (X1 + margin) * pad / k,
        ORIGIN_LAT + (Y1 + margin) * pad / 111_000.0,
    )


def gg_corridor():
    """The Golden Gate corridor as a polygon (list of (x, y))."""
    s0, s1, hw = GG_CORRIDOR
    (sx, sy), (ux, uy) = GG_S, GG_U
    at = lambda s, a: (sx + ux * s - uy * a, sy + uy * s + ux * a)
    return [at(s0, -hw), at(s1, -hw), at(s1, hw), at(s0, hw)]
