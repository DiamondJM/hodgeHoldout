"""Fast mod-p Gauss-Manin engine for the target sector (tau-exponent 0 mod 3) of the triple-cover
fibre surfaces S3: G = y^2 - x^3 - a(rho,tau;c) x - b(rho,tau;c) in P(1,1,6,9).
Returns the connection matrices Gamma_i (nabla_i e_b = sum_a Gamma_i[a,b] e_a) in a fixed
monomial normal-form frame, with first derivatives via dual numbers."""
import sympy as sp, pickle, functools
from flint import nmod_mat, nmod
P = 1000003
rho, tau, x, v, c1, c2, t = sp.symbols('rho tau x v c1 c2 t')
SECTOR = 0

@functools.lru_cache(None)
def symbolic_ab():
    D = pickle.load(open('/home/user/hodgeHoldout/cycleq2/variation.pkl', 'rb'))
    def as_t(expr, vpow): return sp.expand(sp.expand(expr / v**vpow).subs(v, t**sp.Rational(1, 6)))
    def form(F_t, deg): return sp.expand(rho**deg * F_t.subs(t, (tau/rho)**3))
    a, b = form(as_t(D['A'], 0), 12), form(as_t(D['B'], 0), 18)
    def tab(e):  # dict (i_rho, j_tau, k_c1, l_c2) -> Rational
        return {m: cf for m, cf in sp.Poly(e, rho, tau, c1, c2).terms()}
    return tab(a), tab(b)

def inv(z): return pow(int(z) % P, P - 2, P)
def ratmod(cf): return int(sp.numer(cf)) % P * inv(int(sp.denom(cf))) % P

@functools.lru_cache(None)
def modtables():
    ta, tb = symbolic_ab()
    return ({m: ratmod(c) for m, c in ta.items()}, {m: ratmod(c) for m, c in tb.items()})

def eval_form(tab, cc, d):
    """the form and its c-derivatives up to order 2 at cc: returns dict deriv-index -> {(i,j): coeff}"""
    c1v, c2v = cc
    out = {}
    for (di, dj) in ((0,0),(1,0),(0,1),(2,0),(1,1),(0,2)):
        poly = {}
        for (i, j, k, l), cf in tab.items():
            if k < di or l < dj: continue
            fk = 1
            for r in range(di): fk *= (k - r)
            for r in range(dj): fk *= (l - r)
            val = cf * fk % P * pow(c1v, k - di, P) % P * pow(c2v, l - dj, P) % P
            if val: poly[(i, j)] = (poly.get((i, j), 0) + val) % P
        out[(di, dj)] = poly
    return out

def Gpolys(cc):
    """y-free part g = -a x - b of G and its c-derivatives, as dicts (i,j,k)->coeff for rho^i tau^j x^k."""
    ta, tb = modtables()
    A, B = eval_form(ta, cc, 12), eval_form(tb, cc, 18)
    out = {}
    for key in A:
        g = {}
        for (i, j), cf in A[key].items(): g[(i, j, 1)] = (g.get((i, j, 1), 0) - cf) % P
        for (i, j), cf in B[key].items(): g[(i, j, 0)] = (g.get((i, j, 0), 0) - cf) % P
        if key == (0, 0): g[(0, 0, 3)] = (g.get((0, 0, 3), 0) - 1) % P   # the -x^3 term
        out[key] = {m: c for m, c in g.items() if c}
    return out

def pd(poly, var):
    out = {}
    for m, cf in poly.items():
        if m[var] == 0: continue
        mm = list(m); mm[var] -= 1
        out[tuple(mm)] = (out.get(tuple(mm), 0) + cf * m[var]) % P
    return {m: c for m, c in out.items() if c}
def mul(p, q):
    out = {}
    for m1, a in p.items():
        for m2, b in q.items():
            m = (m1[0]+m2[0], m1[1]+m2[1], m1[2]+m2[2]); out[m] = (out.get(m, 0) + a*b) % P
    return {m: c for m, c in out.items() if c}
def add(p, q, s=1):
    out = dict(p)
    for m, c in q.items(): out[m] = (out.get(m, 0) + s*c) % P
    return {m: c for m, c in out.items() if c}
def scal(p, s): return {m: c*s % P for m, c in p.items() if c*s % P}

def monos(d, sector):
    return [(i, d - 6*k - i, k) for k in range(d//6 + 1) for i in range(d - 6*k + 1) if (d - 6*k - i) % 3 == sector]

class Point:
    """Griffiths reduction at a point, with first-order jets (eps1, eps2) of the base."""
    def __init__(self, cc):
        self.cc = cc
        g = Gpolys(cc)
        self.g = g
        # Jacobian generators (y-free): d g / d rho, d g / d tau, d g / d x  (and their eps-jets)
        self.J = {key: [pd(g[key], 0), pd(g[key], 1), pd(g[key], 2)] for key in g}
        self.cache = {}
    def setup(self, d, sector):
        k = (d, sector)
        if k in self.cache: return self.cache[k]
        rows = monos(d, sector); ridx = {m: r for r, m in enumerate(rows)}
        cols = []  # (generator index, monomial)
        for gi, gd in ((0, 17), (1, 17), (2, 12)):
            sec_g = {0: 0, 1: 2, 2: 0}[gi]       # tau-exponent mod 3 of each generator
            for e in monos(d - gd, (sector - sec_g) % 3): cols.append((gi, e))
        def colvec(key, gi, e):
            vec = {}
            for m, cf in self.J[key][gi].items():
                mm = (m[0]+e[0], m[1]+e[1], m[2]+e[2])
                if mm in ridx: vec[ridx[mm]] = (vec.get(ridx[mm], 0) + cf) % P
            return vec
        n = len(rows)
        M0 = nmod_mat(n, len(cols), P)
        for j, (gi, e) in enumerate(cols):
            for r, cf in colvec((0, 0), gi, e).items(): M0[r, j] = cf
        # pivots of M0 (rref)
        R, rk = M0.rref()
        piv = []
        r = 0
        for j in range(len(cols)):
            if r < rk and R[r, j] != 0: piv.append(j); r += 1
        # complement basis monomials: rows not covered -> choose by rref of transpose structure
        # normal-form monomials = greedy monomials independent of column space
        basis = []
        cur = nmod_mat(n, rk, P)
        for jj, j in enumerate(piv):
            for rr in range(n): cur[rr, jj] = M0[rr, j]
        for m in rows:
            if len(basis) == n - rk: break
            test = nmod_mat(n, rk + len(basis) + 1, P)
            for rr in range(n):
                for jj in range(rk): test[rr, jj] = cur[rr, jj]
            for bi, bm in enumerate(basis + [m]): test[ridx[bm], rk + bi] = 1
            if test.rank() == rk + len(basis) + 1: basis.append(m)
        # square system S = [pivot J-columns | basis columns]
        def Smat(key):
            S = nmod_mat(n, n, P)
            for jj, j in enumerate(piv):
                gi, e = cols[j]
                for rr, cf in colvec(key, gi, e).items(): S[rr, jj] = cf
            if key == (0, 0):
                for bi, bm in enumerate(basis): S[ridx[bm], rk + bi] = 1
            return S
        S0 = Smat((0, 0)); S0inv = S0.inv()
        S1, S2 = Smat((1, 0)), Smat((0, 1))
        self.cache[k] = (rows, ridx, cols, piv, basis, S0inv, S1, S2, rk)
        return self.cache[k]
    def solve(self, d, sector, b0, b1, b2):
        """S(eps) X(eps) = b(eps) to first order; returns X0, X1, X2 as nmod_mat columns."""
        rows, ridx, cols, piv, basis, S0inv, S1, S2, rk = self.setup(d, sector)
        X0 = S0inv * b0
        X1 = S0inv * (b1 - S1 * X0)
        X2 = S0inv * (b2 - S2 * X0)
        return X0, X1, X2
    def vec(self, poly, d, sector):
        rows, ridx = self.setup(d, sector)[:2]
        b = nmod_mat(len(rows), 1, P)
        for m, cf in poly.items():
            if cf: b[ridx[m], 0] = (int(b[ridx[m], 0]) + cf) % P
        return b
    def reduce(self, Qj, kpole, sector):
        """Res(Q Omega/G^k) with Q given as jets (Q0, Q1, Q2) -> {(d, basis monomial): (c0, c1, c2)}"""
        out = {}
        Q = Qj
        while kpole >= 1:
            d = 18*kpole - 17
            rows, ridx, cols, piv, basis, S0inv, S1, S2, rk = self.setup(d, sector)
            X = self.solve(d, sector, *(self.vec(q, d, sector) for q in Q))
            for bi, bm in enumerate(basis):
                vals = tuple(int(Xe[rk + bi, 0]) for Xe in X)
                if any(vals):
                    o = out.get((d, bm), (0, 0, 0)); out[(d, bm)] = tuple((o[i] + vals[i]) % P for i in range(3))
            if kpole == 1: break
            # A_j jets, then new numerator sum_j d A_j / d z_j / (k-1)
            newQ = []
            for e_i, Xe in enumerate(X):
                Aj = [dict(), dict(), dict()]
                for jj, j in enumerate(piv):
                    cf = int(Xe[jj, 0])
                    if cf:
                        gi, e = cols[j]; Aj[gi][e] = (Aj[gi].get(e, 0) + cf) % P
                newQ.append(scal(add(add(pd(Aj[0], 0), pd(Aj[1], 1)), pd(Aj[2], 2)), inv(kpole - 1)))
            # jet correction: the A_j themselves were solved with S(eps); X already first-order consistent
            Q = tuple(newQ)
            kpole -= 1
        return out

def frame(pt, sector=SECTOR):
    """normal-form frame of the sector: list of (pole k, monomial)"""
    fr = []
    for kpole in (1, 2, 3):
        d = 18*kpole - 17
        fr += [(kpole, m) for m in pt.setup(d, sector)[4]]
    return fr

def connection(cc, sector=SECTOR):
    """Gamma_i and dGamma_i/dc_j at cc (mod P) in the frame; nabla_i e = -k Res(m dG/dc_i Omega/G^(k+1))."""
    pt = Point(cc)
    fr = frame(pt, sector)
    index = {(18*k - 17, m): n for n, (k, m) in enumerate(fr)}
    N = len(fr)
    G = {(i, j): nmod_mat(N, N, P) for i in (0, 1) for j in (None, 0, 1)}
    for b, (kpole, m) in enumerate(fr):
        mono = {m: 1}
        for i, dkey in enumerate(((1, 0), (0, 1))):
            # numerator jets: -k * m * dG/dc_i at c+eps: value, d/dc1, d/dc2
            d2 = {(1, 0): ((2, 0), (1, 1)), (0, 1): ((1, 1), (0, 2))}[dkey]
            Qj = (scal(mul(mono, pt.g[dkey]), (-kpole) % P),
                  scal(mul(mono, pt.g[d2[0]]), (-kpole) % P),
                  scal(mul(mono, pt.g[d2[1]]), (-kpole) % P))
            red = pt.reduce(Qj, kpole + 1, sector)
            for key, vals in red.items():
                a = index[key]
                G[(i, None)][a, b] = vals[0]; G[(i, 0)][a, b] = vals[1]; G[(i, 1)][a, b] = vals[2]
    return fr, G

if __name__ == '__main__':
    import sys, time
    cc = (2, 3)
    t0 = time.time()
    fr, G = connection(cc)
    print('frame size', len(fr), ' time %.1fs' % (time.time() - t0))
    G1, G2 = G[(0, None)], G[(1, None)]
    flat = G[(1, 0)] - G[(0, 1)] + (G1*G2 - G2*G1)
    print('flatness d1 Gamma2 - d2 Gamma1 + [Gamma1, Gamma2] == 0 :', all(flat[i, j] == 0 for i in range(flat.nrows()) for j in range(flat.ncols())))
    # rank of D-module generated by e_rho (index of (1, rho))
    s = [n for n, (k, m) in enumerate(fr) if k == 1][0]
    N = len(fr)
    def col(M, j):
        c = nmod_mat(N, 1, P)
        for i in range(N): c[i, 0] = M[i, j]
        return c
    e = nmod_mat(N, 1, P); e[s, 0] = 1
    v1, v2 = G1*e, G2*e
    v11 = G[(0, 0)]*e + G1*v1; v12 = G[(0, 1)]*e + G2*v1; v22 = G[(1, 1)]*e + G2*v2
    W = nmod_mat(N, 6, P)
    for j, vv in enumerate((e, v1, v2, v11, v12, v22)):
        for i in range(N): W[i, j] = vv[i, 0]
    print('rank of span{s, d s, d d s} =', W.rank())
