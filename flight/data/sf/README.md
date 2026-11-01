# San Francisco map data

`sf_world.bin` (committed) is the San Francisco collision world:
- terrain on the same 20 m grid as the procedural map;
- about 41,000 convex building prisms;
- OSM street centrelines.

`src/world.rs` embeds it with `include_bytes!`, so the demo and the harness need no network.

## Regenerate

```sh
python3 fetch.py                     # stdlib only: downloads into raw/ (~60 MB, not committed)
pip install shapely && python3 build.py   # writes sf_world.bin
```

## Frame

The map frame is UTM zone 10N (WGS84) easting and northing minus the origin's, in metres. The origin is near Kearny & Market (−122.4050, 37.7910).

- x points east and y points grid north, which is 0.37° from true north.
- The map spans ±3000 m: Alamo Square to Yerba Buena Island, Mission Dolores to Pier 39.
- Heights are NAVD88 metres. Water is held at 1.0 m (about mean sea level); the USGS model flattens the bay to −1.08 m.
- UTM's scale factor here is 0.99963, so distances on the map are 0.04% shorter than on the ground.

`geo.py` holds the projection (Krüger series). It matches pyproj to 0.03 mm.

## Sources

| Data | Source | Licence |
|---|---|---|
| Building footprints and LiDAR heights (2010) | [DataSF Building Footprints](https://data.sfgov.org/Geographic-Locations-and-Boundaries/Building-Footprints/ynuv-fyni) | ODC PDDL |
| Newer buildings and heights, streets, Bay Bridge | © OpenStreetMap contributors, via Overpass | ODbL |
| Bare-earth terrain | USGS 3DEP (1 m, resampled to 20 m) | Public domain |

## How obstacles are built (`build.py`)

Every step only makes obstacles larger, never smaller.

- **Footprints become convex pieces.**
  - A footprint whose convex hull reaches more than 3 m beyond it is cut at reflex vertices, along an edge's extension. That splits L and U shapes into their rectangles.
  - Each piece becomes its convex hull, and courtyards are filled.
  - Hulls are simplified only by dropping an edge and extending its neighbours until they meet, which adds a sliver at most 0.25 m thick.
- **DataSF heights are the maximum LiDAR first return** over each footprint, not the median. The median is wrong for most towers.
- **DataSF's LiDAR is from 2010.** Salesforce Tower shows there as 115 m (it's 326 m), and Park Tower (2018) has no footprint at all.
  - OSM adds every building DataSF lacks and every one it says is taller.
  - An OSM building is dropped only when DataSF footprints at least as tall already cover it.
  - OSM buildings with no height, no storey count and no DataSF footprint get 12 m (446 of them).
  - Underground stations are skipped.
- **The Bay Bridge West Span is one solid curtain.** It runs from the water up to a piecewise-linear envelope over its cables:
  - 160 m at towers W2, W3, W5 and W6;
  - main spans sagging to 100 m;
  - 80 m at the centre anchorage, 60–70 m at the shore anchorages.

  A straight line between two points of a sagging cable lies above the cable. You can't fly under the bridge in this model.
- **Elevated freeways** (I-80, US-101) are curtains from the ground to 24 m above it.

## Known gaps

- **Buildings only change when this file is regenerated.** Heights are 2010 LiDAR plus OSM as of the fetch date.
- **Not modelled:** cranes, light masts, power lines and trees outside building footprints.
- **The bridge and freeway heights are conservative estimates.** They aren't surveyed values.
