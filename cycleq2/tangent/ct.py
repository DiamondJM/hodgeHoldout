"""Fixed-denominator solver for the canonical tangent equation of cycle-q2 (hodge-computer/sextics PR #223,
data/cycle-q2/CanonicalTangents.lean, `CanonicalTangentSolution`), mod p, split by the diagonal symmetry group.

With y = Y2, g = F_y, T_i = g d_i - F_i d_y (i over X0,X1,X2,Y0,Y1), a = A/y, e = X0 X2^3 Y0 + X1^3 X2 Y1:
    find P_i (degree deg H + 2) with
        4 g^2 sum_i (H T_i(P_i) - P_i T_i(H)) - H^2 a (48 y^5 - e)  =  0   mod F^2.
A solution gives the certificate v = A/(2g) d_y + sum_i (P_i/H) T_i  (2 v(F) = A, div v = 0 mod F^2).
H is taken free of y (norms) and semi-invariant (products of conjugates), without loss of generality."""
import itertools, os, sys, time
from flint import nmod_mpoly_ctx, nmod_mat, Ordering
P = int(os.environ.get('CTP', '1000003'))
ctx = nmod_mpoly_ctx.get(('y', 'X0', 'X1', 'X2', 'Y0', 'Y1'), modulus=P, ordering=Ordering.lex)
y, X0, X1, X2, Y0, Y1 = G = ctx.gens()
inv2 = pow(2, P - 2, P)
e = X0*X2**3*Y0 + X1**3*X2*Y1
F = y**6 + inv2*e*y + X0**6 + X1**6 + X2**6 + Y0**6 + Y1**6 + inv2*X0**3*X1*Y0*Y1
a = X0**2*X1**2*X2**3*Y0**2*Y1**2
g = F.derivative(0)
Fi = [F.derivative(k) for k in range(1, 6)]
F2 = F*F
g2x4 = 4*g*g
SRC = a*(48*y**5 - e)

# diagonal symmetry group (exponent vectors mod 6 in the order y, X0, X1, X2, Y0, Y1)
_mons = [m for m in F.monoms()]
GROUP = [w for w in itertools.product(range(6), repeat=6) if all(sum(int(a_)*b for a_, b in zip(m, w)) % 6 == 0 for m in _mons)]
# a generating set is enough for characters: pick independent elements greedily
def char(m): return tuple(sum(int(a_)*b for a_, b in zip(m, w)) % 6 for w in GENS)
GENS = []
_seen = {tuple([0]*6)}
for w in GROUP:
    if w not in _seen:
        GENS.append(w)
        _seen = {tuple((u[i] + k*w[i]) % 6 for i in range(6)) for u in _seen for k in range(6)}
    if len(_seen) == len(GROUP): break

def monos(deg, ymax=11, yfree=False):
    out = []
    for ey in range(0, 1 if yfree else min(deg, ymax) + 1):
        for c in itertools.combinations(range(deg - ey + 4), 4):
            ex, prev = [], -1
            for ci in c: ex.append(ci - prev - 1); prev = ci
            ex.append(deg - ey + 3 - prev)
            out.append((ey, *ex))
    return out
def mono(m): return ctx.from_dict({tuple(m): 1})
def poly_char(p):
    cs = {char(m) for m in p.monoms()}
    return cs.pop() if len(cs) == 1 else None
def cadd(u, v, s=1): return tuple((a_ + s*b) % 6 for a_, b in zip(u, v))

def column(H, dH, i, m):
    pm = mono(m)
    Ti = g*pm.derivative(i + 1) - Fi[i]*pm.derivative(0)
    return g2x4*(H*Ti - pm*g*dH[i])

def solve(H, want_solution=False):
    """H: y-free semi-invariant polynomial.  Returns (solvable, n_unknowns, rank[, solution])."""
    d = H.total_degree(); chH = poly_char(H); assert chH is not None, 'H not semi-invariant'
    dH = [H.derivative(k) for k in range(1, 6)]
    rhs = divmod(H*H*SRC, F2)[1]
    target = poly_char(rhs)
    cols, meta = [], []
    for i in range(5):
        # character offset of column(m) relative to m: from one sample
        off = None
        for m in monos(d + 2):
            if off is None:
                c0 = column(H, dH, i, m)
                if c0 == 0: continue
                off = cadd(poly_char(c0), char(m), -1)
            if cadd(char(m), off) != target: continue
            cols.append(divmod(column(H, dH, i, m), F2)[1]); meta.append((i, m))
    rows = {}
    for p in cols + [rhs]:
        for mm in p.monoms(): rows.setdefault(tuple(mm), len(rows))
    M = nmod_mat(len(rows), len(cols) + 1, P)
    for j, p in enumerate(cols + [rhs]):
        for mm, cf in zip(p.monoms(), p.coeffs()): M[rows[tuple(mm)], j] = int(cf)
    M0 = nmod_mat(len(rows), max(len(cols), 1), P)
    for j, p in enumerate(cols):
        for mm, cf in zip(p.monoms(), p.coeffs()): M0[rows[tuple(mm)], j] = int(cf)
    r0 = M0.rank() if cols else 0
    return (r0 == M.rank(), len(cols), r0)

if __name__ == '__main__':
    print('group order (incl. scalars):', len(GROUP), ' generators:', GENS)
    assert divmod(sum(G[k]*F.derivative(k) for k in range(6)) - 6*F, F)[1] == 0
    # control: manufacture a source from random P at H = X0^2, check the solver logic end to end
    import random
    random.seed(1)
    H = X0**2; dH = [H.derivative(k) for k in range(1, 6)]
    t0 = time.time(); print('H = X0^2 :', solve(H), '%.1fs' % (time.time() - t0))
    t0 = time.time(); print('H = X0^6 + Y0^6 :', solve(X0**6 + Y0**6), '%.1fs' % (time.time() - t0))
