"""Where Luis Pabon's procedural city (the gate's map, seed 1337) sits on Earth for X-Plane.

The map is 6 km square, x east, y north, metres from (0, 0). We put (0, 0) on the water of the south Bay so the
terrain mesh (3 to 927 m) and the buildings have nothing of X-Plane's own underneath. One flat-earth formula is
used by the scenery builder, the sidecar's display and the coarse filter's state, so all three agree.
"""
import math

ORIGIN_LAT, ORIGIN_LON = 37.56, -122.17
R = 6_371_000.0
_KX = R * math.cos(math.radians(ORIGIN_LAT)) * math.pi / 180
_KY = R * math.pi / 180


def to_geo(x, y):
    """map metres -> (lat, lon)."""
    return ORIGIN_LAT + y / _KY, ORIGIN_LON + x / _KX


def to_map(lat, lon):
    """(lat, lon) -> map metres (x east, y north)."""
    return (lon - ORIGIN_LON) * _KX, (lat - ORIGIN_LAT) * _KY


if __name__ == "__main__":
    lat, lon = to_geo(-1500.0, 60.0)
    x, y = to_map(lat, lon)
    assert abs(x + 1500) < 1e-6 and abs(y - 60) < 1e-6
    print("gridmap ok", lat, lon)
