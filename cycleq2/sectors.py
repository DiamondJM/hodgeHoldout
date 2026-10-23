"""Sector dimensions of the weighted Jacobian ring and of the Kodaira-Spencer maps at (c1,c2).
Sector of Res(Q Omega/G^k) = (tau-exponent of Q) + 1 mod 3; the target sector is tau-exponent 0 mod 3."""
import sympy as sp, pickle, sys
from flint import fmpq_mat, fmpq
rho, tau, x, v, c1, c2, t = sp.symbols('rho tau x v c1 c2 t')
D = pickle.load(open('variation.pkl', 'rb'))
C1, C2 = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (2, 3)
def as_t_sym(expr, vpow): return sp.expand(sp.expand(expr / v**vpow).subs(v, t**sp.Rational(1, 6)))
def form(F_t, deg): return sp.expand(rho**deg * F_t.subs(t, (tau/rho)**3))
As, Bs = as_t_sym(D['A'], 0), as_t_sym(D['B'], 0); sub = {c1: C1, c2: C2}
a, b = form(As.subs(sub), 12), form(Bs.subs(sub), 18)
Gc = [sp.expand(-form(sp.diff(As, c).subs(sub), 12)*x - form(sp.diff(Bs, c).subs(sub), 18)) for c in (c1, c2)]
J = [(sp.expand(-sp.diff(a, rho)*x - sp.diff(b, rho)), 17), (sp.expand(-sp.diff(a, tau)*x - sp.diff(b, tau)), 17),
     (sp.expand(-3*x**2 - a), 12)]
def monos(d, s=None):
    out = [(i, d - 6*k - i, k) for k in range(d//6 + 1) for i in range(d - 6*k + 1)] if d >= 0 else []
    return [m for m in out if s is None or m[1] % 3 == s]
def mono(e): return rho**e[0]*tau**e[1]*x**e[2]
def span_rank(polys, d, s):
    rows = {m: r for r, m in enumerate(monos(d, s))}
    if not polys: return 0, len(rows)
    M = fmpq_mat(len(rows), len(polys))
    for j, p in enumerate(polys):
        for mon, cf in sp.Poly(p, rho, tau, x).terms():
            if mon in rows: M[rows[mon], j] = fmpq(int(sp.numer(cf)), int(sp.denom(cf)))
    return M.rank(), len(rows)
def J_part(d, s):   # J_d restricted to sector s (all generators are tau^3-homogeneous up to their own tau-degree)
    out = []
    for g, gd in J:
        for e in monos(d - gd):
            p = sp.expand(g*mono(e))
            # project to sector s: keep monomials with tau-exponent = s mod 3
            pp = sum(cf*mono(m) for m, cf in sp.Poly(p, rho, tau, x).terms() if m[1] % 3 == s)
            if pp != 0: out.append(pp)
    return out
for d in (1, 19, 37):
    for s in (0, 1, 2):
        rJ, n = span_rank(J_part(d, s), d, s)
        print(f'R_{d} sector tau^{s} (class sector omega^{(s+1)%3}): dim {n - rJ}', flush=True)
# KS maps in the target sector (tau-exponent 0 mod 3): R_1 -> R_19 and R_19 -> R_37, both directions c1, c2
for (dsrc, dtgt) in ((1, 19), (19, 37)):
    s = 0
    src = [mono(e) for e in monos(dsrc, s)]
    imgs = [sp.expand(g*q) for g in Gc for q in src]
    rJ, n = span_rank(J_part(dtgt, s), dtgt, s)
    rJK, _ = span_rank(J_part(dtgt, s) + imgs, dtgt, s)
    print(f'KS: R_{dsrc} -> R_{dtgt} (target sector): image dim {rJK - rJ} of {n - rJ}')
