"""Arbitrary-order jets of the target-sector Gauss-Manin connection (mod P), built on gm_engine.
Taylor coefficients in eps = c - c0 up to total order m."""
import functools, itertools
from flint import nmod_mat
from gm_engine import (P, inv, modtables, pd, mul, add, scal, monos, SECTOR)
from math import comb, factorial

def multi(m): return [(i, j) for s in range(m + 1) for i in range(s + 1) for j in [s - i]]

def taylor_form(tab, cc, m):
    """Taylor coefficients {(i,j) : {(r,t): coeff}} of the form at cc + eps, |(i,j)| <= m."""
    c1v, c2v = cc
    out = {al: {} for al in multi(m)}
    for (r, tt, k, l), cf in tab.items():
        for (i, j) in multi(m):
            if i > k or j > l: continue
            val = cf * comb(k, i) % P * comb(l, j) % P * pow(c1v, k - i, P) % P * pow(c2v, l - j, P) % P
            if val:
                d = out[(i, j)]; d[(r, tt)] = (d.get((r, tt), 0) + val) % P
    return out

class JetPoint:
    def __init__(self, cc, m):
        self.cc, self.m = cc, m
        ta, tb = modtables()
        A, B = taylor_form(ta, cc, m + 1), taylor_form(tb, cc, m + 1)
        self.g = {}
        for al in multi(m + 1):
            gpoly = {}
            for (r, tt), cf in A[al].items(): gpoly[(r, tt, 1)] = (gpoly.get((r, tt, 1), 0) - cf) % P
            for (r, tt), cf in B[al].items(): gpoly[(r, tt, 0)] = (gpoly.get((r, tt, 0), 0) - cf) % P
            if al == (0, 0): gpoly[(0, 0, 3)] = (gpoly.get((0, 0, 3), 0) - 1) % P
            self.g[al] = {k: v for k, v in gpoly.items() if v}
        self.J = {al: [pd(self.g[al], 0), pd(self.g[al], 1), pd(self.g[al], 2)] for al in multi(m)}
        self.cache = {}
    def setup(self, d, sector):
        key = (d, sector)
        if key in self.cache: return self.cache[key]
        rows = monos(d, sector); ridx = {mm: r for r, mm in enumerate(rows)}
        cols = []
        for gi, gd in ((0, 17), (1, 17), (2, 12)):
            sec_g = {0: 0, 1: 2, 2: 0}[gi]
            for e in monos(d - gd, (sector - sec_g) % 3): cols.append((gi, e))
        def colvec(al, gi, e):
            vec = {}
            for mm, cf in self.J[al][gi].items():
                t = (mm[0] + e[0], mm[1] + e[1], mm[2] + e[2])
                if t in ridx: vec[ridx[t]] = (vec.get(ridx[t], 0) + cf) % P
            return vec
        n = len(rows)
        M0 = nmod_mat(n, max(len(cols), 1), P)
        for j, (gi, e) in enumerate(cols):
            for r, cf in colvec((0, 0), gi, e).items(): M0[r, j] = cf
        R, rk = M0.rref()
        piv, r = [], 0
        for j in range(len(cols)):
            if r < rk and R[r, j] != 0: piv.append(j); r += 1
        basis = []
        for mm in rows:
            if len(basis) == n - rk: break
            test = nmod_mat(n, rk + len(basis) + 1, P)
            for rr in range(n):
                for jj, j in enumerate(piv): test[rr, jj] = M0[rr, j]
            for bi, bm in enumerate(basis + [mm]): test[ridx[bm], rk + bi] = 1
            if test.rank() == rk + len(basis) + 1: basis.append(mm)
        S = {}
        for al in multi(self.m):
            Sm = nmod_mat(n, n, P)
            for jj, j in enumerate(piv):
                gi, e = cols[j]
                for rr, cf in colvec(al, gi, e).items(): Sm[rr, jj] = cf
            if al == (0, 0):
                for bi, bm in enumerate(basis): Sm[ridx[bm], rk + bi] = 1
            S[al] = Sm
        S0inv = S[(0, 0)].inv() if n else None
        self.cache[key] = (rows, ridx, cols, piv, basis, S0inv, S, rk)
        return self.cache[key]
    def vec(self, poly, d, sector):
        rows, ridx = self.setup(d, sector)[:2]
        b = nmod_mat(len(rows), 1, P)
        for mm, cf in poly.items():
            if cf: b[ridx[mm], 0] = (int(b[ridx[mm], 0]) + cf) % P
        return b
    def reduce(self, Q, kpole, sector):
        """Q: {alpha: poly} Taylor jets of the numerator; returns {(d, mono): {alpha: coeff}}"""
        out = {}
        al_list = multi(self.m)
        while kpole >= 1:
            d = 18 * kpole - 17
            rows, ridx, cols, piv, basis, S0inv, S, rk = self.setup(d, sector)
            if not rows: break
            B = {al: self.vec(Q.get(al, {}), d, sector) for al in al_list}
            X = {}
            for al in al_list:                         # increasing total order
                rhs = B[al]
                for be in al_list:
                    if be == (0, 0) or be[0] > al[0] or be[1] > al[1]: continue
                    ga = (al[0] - be[0], al[1] - be[1])
                    rhs = rhs - S[be] * X[ga]
                X[al] = S0inv * rhs
            for bi, bm in enumerate(basis):
                for al in al_list:
                    v = int(X[al][rk + bi, 0])
                    if v:
                        o = out.setdefault((d, bm), {}); o[al] = (o.get(al, 0) + v) % P
            if kpole == 1: break
            newQ = {}
            for al in al_list:
                Aj = [dict(), dict(), dict()]
                for jj, j in enumerate(piv):
                    cf = int(X[al][jj, 0])
                    if cf:
                        gi, e = cols[j]; Aj[gi][e] = (Aj[gi].get(e, 0) + cf) % P
                newQ[al] = scal(add(add(pd(Aj[0], 0), pd(Aj[1], 1)), pd(Aj[2], 2)), inv(kpole - 1))
            Q = newQ
            kpole -= 1
        return out

def connection_jets(cc, m, sector=SECTOR):
    """Taylor jets (order <= m) of Gamma_1, Gamma_2 in the normal-form frame."""
    pt = JetPoint(cc, m)
    fr = []
    for kpole in (1, 2, 3):
        fr += [(kpole, mm) for mm in pt.setup(18 * kpole - 17, sector)[4]]
    index = {(18 * k - 17, mm): n for n, (k, mm) in enumerate(fr)}
    N = len(fr)
    Gam = {i: {al: nmod_mat(N, N, P) for al in multi(m)} for i in (0, 1)}
    for b, (kpole, mm) in enumerate(fr):
        for i in (0, 1):
            # Taylor jets of d G / d c_i at c0 + eps: coefficient of eps^al is (al_i + 1) * g[al + e_i]
            Q = {}
            for al in multi(m):
                up = (al[0] + 1, al[1]) if i == 0 else (al[0], al[1] + 1)
                fac = (up[i]) % P
                Q[al] = scal(mul({mm: 1}, self_g := pt.g[up]), (-kpole * fac) % P)
            red = pt.reduce(Q, kpole + 1, sector)
            for key, jets in red.items():
                a = index[key]
                for al, v in jets.items(): Gam[i][al][a, b] = v
    return fr, Gam

def derivative_span(cc, maxorder, sector=SECTOR):
    """ranks of span{nabla^alpha s : |alpha| <= k} for k <= maxorder, s = Res(rho Omega/G)."""
    m = maxorder - 1
    fr, Gam = connection_jets(cc, m, sector)
    N = len(fr)
    s_idx = [n for n, (k, mm) in enumerate(fr) if k == 1][0]
    # a section is a Taylor jet {al: column}; nabla_i u = d_{eps_i} u + Gamma_i(eps) u, truncated
    def nab(u, i, order):
        out = {}
        for al in multi(order):
            up = (al[0] + 1, al[1]) if i == 0 else (al[0], al[1] + 1)
            col = nmod_mat(N, 1, P)
            if up in u: col = col + u[up] * nmod((up[i]), P) if False else col
            if up in u:
                for r in range(N): col[r, 0] = (int(col[r, 0]) + int(u[up][r, 0]) * up[i]) % P
            for be in multi(order):
                if be[0] > al[0] or be[1] > al[1]: continue
                ga = (al[0] - be[0], al[1] - be[1])
                if be in Gam[i] and ga in u: col = col + Gam[i][be] * u[ga]
            out[al] = col
        return out
    e = nmod_mat(N, 1, P); e[s_idx, 0] = 1
    layer = {(): {al: (e if al == (0, 0) else nmod_mat(N, 1, P)) for al in multi(m + 1)}}
    vecs = [e]; ranks = []
    for k in range(1, maxorder + 1):
        new = {}
        for word, u in layer.items():
            for i in (0, 1):
                w2 = tuple(sorted(word + (i,)))
                if w2 not in new: new[w2] = nab(u, i, m + 1 - k)
        layer = new
        vecs += [u[(0, 0)] for u in layer.values()]
        W = nmod_mat(N, len(vecs), P)
        for j, vv in enumerate(vecs):
            for r in range(N): W[r, j] = vv[r, 0]
        ranks.append(W.rank())
    return ranks

if __name__ == '__main__':
    import sys, time
    cc = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (2, 3)
    K = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    t0 = time.time()
    fr, Gam = connection_jets(cc, 1)
    G1, G2 = Gam[0][(0, 0)], Gam[1][(0, 0)]
    flat = Gam[1][(1, 0)] - Gam[0][(0, 1)] + (G1 * G2 - G2 * G1)
    print('flatness:', all(flat[i, j] == 0 for i in range(flat.nrows()) for j in range(flat.ncols())))
    print(f'(c1,c2)={cc}: ranks of span of derivatives of orders <= 1..{K}:', derivative_span(cc, K),
          ' (%.0fs)' % (time.time() - t0))
