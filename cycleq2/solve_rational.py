"""Search rational G = N/(t^j Delta^k) with G' + G/(3t) + M G = H (exact over Q, flint)."""
import sympy as sp, pickle, sys
from flint import fmpq_mat, fmpq
t = sp.Symbol('t')
C1, C2, a, b, M, H, Delta = pickle.load(open(sys.argv[1], 'rb'))
Dp = sp.Poly(sp.numer(sp.together(Delta)), t)          # integer polynomial, same roots
Dl = Dp.as_expr()
def residual(Nvec, j, k, withH):
    Q = t**j * Dl**k
    G = sp.Matrix(Nvec)/Q
    R = G.diff(t) + G/(3*t) + M*G - (H if withH else sp.zeros(2, 1))
    W = 18 * t**(j+1) * Dl**(k+2)
    return [sp.Poly(sp.cancel(sp.together(W*r)), t) for r in R]
def run(j, k, n):
    cols, rows = [], {}
    basis = [(c, m) for c in (0, 1) for m in range(n+1)]
    for (c, m) in basis:
        Nv = [0, 0]; Nv[c] = t**m
        cols.append(residual(Nv, j, k, False))
    rhs = residual([0, 0], j, k, True)        # = -W H
    def key(i, mon): 
        if (i, mon) not in rows: rows[(i, mon)] = len(rows)
        return rows[(i, mon)]
    entries = []
    for ci, col in enumerate(cols + [rhs]):
        for i in (0, 1):
            for mon, cf in col[i].terms():
                entries.append((key(i, mon), ci, cf))
    nr, nc = len(rows), len(cols)
    Mfull = fmpq_mat(nr, nc+1); M0 = fmpq_mat(nr, nc)
    for r, c, cf in entries:
        Mfull[r, c] = fmpq(int(sp.numer(cf)), int(sp.denom(cf)))
        if c < nc: M0[r, c] = fmpq(int(sp.numer(cf)), int(sp.denom(cf)))
    r0, r1 = M0.rank(), Mfull.rank()
    return r0, r1, nc, nr
for (j, k, n) in [(1, 1, 16), (2, 1, 20), (3, 2, 32), (4, 2, 40)]:
    r0, r1, nc, nr = run(j, k, n)
    print(f'(c1,c2)=({C1},{C2}) j={j} k={k} deg N<={n}: unknowns {nc}, rank {r0}, augmented {r1} ->',
          'RATIONAL SOLUTION' if r0 == r1 else 'no rational solution', flush=True)
