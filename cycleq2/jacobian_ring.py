"""(0,2)-test: is the cubic-pole numerator P of the transported q=2 source zero in R_37 of the
weighted elliptic surface S3: y^2 = x^3 + a(rho,tau) x + b(rho,tau) in P(1,1,6,9), degree 18?"""
import sympy as sp, pickle, sys, itertools
from flint import fmpq_mat, fmpq
rho, tau, x, v, c1, c2, t = sp.symbols('rho tau x v c1 c2 t')
D = pickle.load(open('variation.pkl', 'rb'))
C1, C2 = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (2, 3)
def as_t(expr, vpow):
    e = sp.expand(sp.expand(expr.subs({c1: C1, c2: C2})) / v**vpow)
    return sp.expand(e.subs(v, t**sp.Rational(1, 6)))
q = {k: as_t(D[k], p) for k, p in (('A',0),('B',0),('A1',3),('B1',3),('A2',2),('B2',2),('B12',5))}
def form(F_t, deg):     # homogenise a polynomial in t = (tau/rho)^3 to a form of degree deg in (rho, tau)
    return sp.expand(rho**deg * F_t.subs(t, (tau/rho)**3))
a, b = form(q['A'], 12), form(q['B'], 18)
gens = [sp.expand(-sp.diff(a, rho)*x - sp.diff(b, rho)), sp.expand(-sp.diff(a, tau)*x - sp.diff(b, tau)),
        sp.expand(-3*x**2 - a)]
gdeg = [17, 17, 12]
def monos(d):
    return [(i, j, k) for k in range(d//6 + 1) for i in range(d - 6*k + 1) for j in [d - 6*k - i]]
def mono(e): return rho**e[0]*tau**e[1]*x**e[2]
def quotient_dim_and_test(d, P=None):
    rows = {m: r for r, m in enumerate(monos(d))}
    cols = []
    for g, gd in zip(gens, gdeg):
        for e in monos(d - gd):
            cols.append(sp.Poly(sp.expand(g*mono(e)), rho, tau, x))
    def vec(poly):
        out = {}
        for mon, cf in poly.terms(): out[rows[mon]] = cf
        return out
    vs = [vec(c) for c in cols]
    M = fmpq_mat(len(rows), len(vs))
    for j, vv in enumerate(vs):
        for r, cf in vv.items(): M[r, j] = fmpq(int(sp.numer(cf)), int(sp.denom(cf)))
    rk = M.rank() if vs else 0
    res = len(rows) - rk
    if P is None: return res
    pv = vec(sp.Poly(P, rho, tau, x))
    M2 = fmpq_mat(len(rows), len(vs) + 1)
    for j, vv in enumerate(vs):
        for r, cf in vv.items(): M2[r, j] = fmpq(int(sp.numer(cf)), int(sp.denom(cf)))
    for r, cf in pv.items(): M2[r, len(vs)] = fmpq(int(sp.numer(cf)), int(sp.denom(cf)))
    return res, M2.rank() == rk
for d in (1, 19, 37, 38, 39):
    print(f'(c1,c2)=({C1},{C2})  dim R_{d} =', quotient_dim_and_test(d), flush=True)
# P: 3 tau^3 * (3/4) (A1~ x + B1~)(A2~ x + B2~), the q=2 cubic-pole numerator (overall constants irrelevant)
Pt = sp.expand(3*tau**3*sp.Rational(3, 4)*((q['A1']*x + q['B1'])*(q['A2']*x + q['B2'])).subs(t, tau**3))
Ph = sp.expand(sum(term*rho**(37 - sp.Poly(term, tau, x).monoms()[0][0] - 6*sp.Poly(term, tau, x).monoms()[0][1])
                   for term in sp.Add.make_args(Pt)))
res, inJ = quotient_dim_and_test(37, Ph)
print('P in J_37 (zero (0,2)-component):', inJ)
pickle.dump((C1, C2, Ph), open(f'P37_{C1}_{C2}.pkl', 'wb'))
