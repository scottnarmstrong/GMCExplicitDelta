#!/usr/bin/env python3
"""Print the modules GMCExplicitDelta.Certificates.* in dependency order (one per line), so that they
can be compiled one at a time: some of them need about 12 GB of memory each."""
import glob, re
mods = {}
for f in sorted(glob.glob('GMCExplicitDelta/Certificates/*.lean')):
    m = f[:-5].replace('/', '.')
    mods[m] = re.findall(r'^public import (GMCExplicitDelta\.Certificates\.\S+)', open(f).read(), re.M)
order, seen = [], set()
def visit(m):
    if m in seen:
        return
    seen.add(m)
    for d in mods.get(m, []):
        visit(d)
    order.append(m)
for m in mods:
    visit(m)
print('\n'.join(order))
