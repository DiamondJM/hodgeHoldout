import itertools, time
from core4 import *
cands = []
def add(n, D): cands.append((n, D))
six = [X0**6, X1**6, Y0**6, Y1**6]
for k in (1, 2, 3):
    for S in itertools.combinations(range(4), k): add('pow' + ''.join(map(str, S)), sum(six[i] for i in S))
add('hX', hX); add('hY', hY); add('hX+CPL', hX + CPL); add('hY+CPL', hY + CPL); add('CPL', CPL)
add('hX*hY', hX*hY); add('hX-hY', hX - hY)
for e in itertools.product(range(3), repeat=4):
    if 1 <= sum(e) <= 4: add('mono' + ''.join(map(str, e)), ctx.from_dict({e: 1}))
for a, b in itertools.combinations(range(4), 2):
    for sg in (1, -1):
        add(f'{V[a]}^2{"+" if sg>0 else "-"}{V[b]}^2', V[a]**2 + sg*V[b]**2)
        add(f'{V[a]}^3{"+" if sg>0 else "-"}{V[b]}^3', V[a]**3 + sg*V[b]**3)
        add(f'{V[a]}^6{"+" if sg>0 else "-"}{V[b]}^6 * X0', (V[a]**6 + sg*V[b]**6))
for name, D in [('dH/dX0', H.derivative(0)), ('dH/dX1', H.derivative(1)), ('dH/dY0', H.derivative(2)), ('dH/dY1', H.derivative(3)),
                ('X0 dH/dX0 + X1 dH/dX1', X0*H.derivative(0) + X1*H.derivative(1)),
                ('X0 dH/dX0 - Y0 dH/dY0', X0*H.derivative(0) - Y0*H.derivative(2))]:
    add(name, D)
t0 = time.time(); hits = []
for n, D in cands:
    ok, nc, r = solvable(H, A, D)
    if ok: hits.append(n)
print(f'{len(cands)} candidate denominators (degrees 1..12) tested in {time.time()-t0:.0f}s; solvable: {hits or "none"}')
