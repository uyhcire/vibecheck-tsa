"""The proposed heading-gain schedule (docs/escape-law-terminal.md, proposal) in the climb: settling of the
straight escape from the 48 representative starts (design.py), terminal law with and without the schedule."""
import numpy as np
from tsmap import TsMap
from terminal import NEW
from design import reference, settle, stats

m = TsMap(); m.smooth(True)
for name, g in (("terminal law", dict(NEW, hLevel=float("nan"))), ("with KPSI schedule", dict(NEW, hLevel=float("nan"), kpsiV=35.2))):
    m.cand(**g)
    ref = reference(m)
    print(name, stats(settle(m, ref)), flush=True)
