"""Degrees in c1 (c2 fixed) of the Gauss-Manin connection entries, by rational reconstruction mod P."""
import time, sys
from flint import nmod_mat
from gm_engine import P, inv
from gm_jets import connection_jets
C2 = int(sys.argv[1]) if len(sys.argv) > 1 else 3
NPTS = int(sys.argv[2]) if len(sys.argv) > 2 else 140
t0 = time.time()
pts, data = [], []
for c1v in range(1, NPTS + 1):
    fr, Gam = connection_jets((c1v, C2), 0)
    pts.append(c1v); data.append((Gam[0][(0, 0)], Gam[1][(0, 0)]))
print('evaluated %d points in %.0fs, frame size %d' % (NPTS, time.time() - t0, len(fr)))
def ratrec(xs, ys, maxdeg):
    """smallest total degree n+d with N/D fitting all points (D monic-normalised); returns (n, d) or None"""
    for tot in range(0, maxdeg + 1):
        for d in range(0, tot + 1):
            n = tot - d
            if n + d + 2 > len(xs) - 5: return None
            M = nmod_mat(len(xs), n + 1 + d + 1, P)
            for r, (xv, yv) in enumerate(zip(xs, ys)):
                p = 1
                for k in range(n + 1): M[r, k] = p; p = p * xv % P
                p = 1
                for k in range(d + 1): M[r, n + 1 + k] = (-yv * p) % P; p = p * xv % P
            if M.rank() < n + d + 2:      # nontrivial kernel -> a fit exists
                return (n, d)
    return None
N = len(fr)
worst = (0, 0); denoms = {}
for which in (0, 1):
    for a in range(N):
        for b in range(N):
            ys = [int(data[k][which][a, b]) for k in range(NPTS)]
            if all(y == 0 for y in ys): continue
            r = ratrec(pts, ys, NPTS - 10)
            if r is None: print('entry', which, a, b, 'not reconstructed'); continue
            if sum(r) > sum(worst): worst = r
            denoms[r[1]] = denoms.get(r[1], 0) + 1
print(f'c2={C2}: max (num deg, den deg) over entries = {worst};  denominator-degree histogram {sorted(denoms.items())}')
