# Texture sources

All sets are from [ambientCG](https://ambientcg.com) and are released under
[CC0 1.0 Universal](https://creativecommons.org/publicdomain/zero/1.0/) (public domain).
`fetch.py` downloads the 1K JPG archives and repacks each set as `albedo.jpg`,
`normal.jpg` (OpenGL convention) and `orm.jpg` (R occlusion, G roughness, B metalness).

| Directory | ambientCG asset | URL |
|---|---|---|
| facade_glass | Facade001 | https://ambientcg.com/view?id=Facade001 |
| facade_grid | Facade006 | https://ambientcg.com/view?id=Facade006 |
| facade_office | Facade012 | https://ambientcg.com/view?id=Facade012 |
| facade_brick | Facade018A | https://ambientcg.com/view?id=Facade018A |
| facade_stone | Facade019A | https://ambientcg.com/view?id=Facade019A |
| facade_brown | Facade020A | https://ambientcg.com/view?id=Facade020A |
| asphalt | Asphalt033 | https://ambientcg.com/view?id=Asphalt033 |
| grass | Grass004 | https://ambientcg.com/view?id=Grass004 |
| rock | Rock030 | https://ambientcg.com/view?id=Rock030 |
| concrete | Concrete034 | https://ambientcg.com/view?id=Concrete034 |
| gravel | Gravel023 | https://ambientcg.com/view?id=Gravel023 |

Without these files the renderer falls back to procedural stand-ins.
