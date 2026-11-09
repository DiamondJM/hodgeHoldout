"""For each open instance: which coordinate reflections Z_i -> -Z_i and scaled swaps
(Z_i, Z_j) -> (z Z_j, Z_i / z), z^6 = 1 (both are reflections) preserve F?  Numerical test at random points."""
import sys, cmath, random, itertools, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fixed_d import parse_rec
root = '/home/user/sextics/data'
cat = json.load(open(root + '/catalogue.json'))['instanceIds']
open_ids = [i for i in cat if not os.path.exists(f'{root}/{i}/acceptance.json')]
names = ['X0', 'X1', 'X2', 'Y0', 'Y1', 'Y2']
random.seed(3)
pts = [[complex(random.uniform(-1, 1), random.uniform(-1, 1)) for _ in range(6)] for _ in range(4)]
def ev(Fd, z):
    return sum((int(c.p) / int(c.q)) * __import__("math").prod(z[i]**int(e[i]) for i in range(6)) for e, c in Fd.items())
for inst in open_ids:
    F, q, A = parse_rec(f'{root}/{inst}/instance.rec')
    Fd = F.to_dict()
    base = [ev(Fd, z) for z in pts]
    found = {'X': [], 'Y': []}
    def same(mapz):
        return all(abs(ev(Fd, mapz(z)) - b) < 1e-9 * (1 + abs(b)) for z, b in zip(pts, base))
    for i in range(6):
        def m(z, i=i): w = list(z); w[i] = -w[i]; return w
        if same(m): found['X' if i < 3 else 'Y'].append(f'{names[i]}->-{names[i]}')
    for blk, idx in (('X', (0, 1, 2)), ('Y', (3, 4, 5))):
        for i, j in itertools.combinations(idx, 2):
            for k in range(6):
                zeta = cmath.exp(2j * cmath.pi * k / 6)
                def m(z, i=i, j=j, zeta=zeta): w = list(z); w[i], w[j] = zeta * z[j], z[i] / zeta; return w
                if same(m): found[blk].append(f'{names[i]}<->z^{k}{names[j]}')
    ok = bool(found['X']) and bool(found['Y'])
    print(f'{inst:28} X-reflections {found["X"] or "-"}  Y-reflections {found["Y"] or "-"}  {"<== TWO-REFLECTION" if ok else ""}')
