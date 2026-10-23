"""Is the (0,2)-component absorbed by base Gauss-Manin (Kodaira-Spencer) terms?
Test P in J_37 + dG/dc1 * S_19 + dG/dc2 * S_19 at (c1,c2)."""
import sympy as sp, pickle, sys
from flint import fmpq_mat, fmpq
rho, tau, x, v, c1, c2, t = sp.symbols('rho tau x v c1 c2 t')
D = pickle.load(open('variation.pkl', 'rb'))
C1, C2 = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (2, 3)
def as_t_sym(expr, vpow):
    e = sp.expand(expr / v**vpow); return sp.expand(e.subs(v, t**sp.Rational(1, 6)))
def form(F_t, deg): return sp.expand(rho**deg * F_t.subs(t, (tau/rho)**3))
Asym, Bsym = as_t_sym(D['A'], 0), as_t_sym(D['B'], 0)
sub = {c1: C1, c2: C2}
a, b = form(Asym.subs(sub), 12), form(Bsym.subs(sub), 18)
Gc = [sp.expand(-form(sp.diff(Asym, c).subs(sub), 12)*x - form(sp.diff(Bsym, c).subs(sub), 18)) for c in (c1, c2)]
gens = [(sp.expand(-sp.diff(a, rho)*x - sp.diff(b, rho)), 17), (sp.expand(-sp.diff(a, tau)*x - sp.diff(b, tau)), 17),
        (sp.expand(-3*x**2 - a), 12)]
def monos(d): return [(i, d - 6*k - i, k) for k in range(d//6 + 1) for i in range(d - 6*k + 1)] if d >= 0 else []
def mono(e): return rho**e[0]*tau**e[1]*x**e[2]
d = 37
rows = {m: r for r, m in enumerate(monos(d))}
def cols_for(polys):
    out = []
    for g, gd in polys:
        for e in monos(d - gd): out.append(sp.Poly(sp.expand(g*mono(e)), rho, tau, x))
    return out
def rank(cols, extra=None):
    allc = cols + ([extra] if extra is not None else [])
    M = fmpq_mat(len(rows), len(allc))
    for j, p in enumerate(allc):
        for mon, cf in p.terms(): M[rows[mon], j] = fmpq(int(sp.numer(cf)), int(sp.denom(cf)))
    return M.rank()
C_J = cols_for(gens)
C_KS = cols_for([(Gc[0], 18), (Gc[1], 18)])
P = pickle.load(open(f'P37_{C1}_{C2}.pkl', 'rb'))[2]
Pp = sp.Poly(P, rho, tau, x)
rJ, rJKS = rank(C_J), rank(C_J + C_KS)
print(f'(c1,c2)=({C1},{C2}): dim R_37 = {len(rows)-rJ};  dim R_37/(KS images) = {len(rows)-rJKS}')
print('P in J_37:', rank(C_J, Pp) == rJ, '   P in J_37 + KS:', rank(C_J + C_KS, Pp) == rJKS)
