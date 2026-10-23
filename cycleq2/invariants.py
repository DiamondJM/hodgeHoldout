"""Aronhold invariants of U = a x^3 + b y^3 + c z^3 + d x^2 y + e y^2 z + f z^2 x + m x y z,
normalised to cycle-three's s4, s6 at m = 0, via the Hessian syzygy H(H(U)) = lam U + mu H(U)."""
import sympy as sp, pickle
x, y, z, a, b, c, d, e, f, m = sp.symbols('x y z a b c d e f m')
U = a*x**3 + b*y**3 + c*z**3 + d*x**2*y + e*y**2*z + f*z**2*x + m*x*y*z
hess = lambda P: sp.expand(sp.Matrix(3, 3, lambda i, j: sp.diff(P, [x, y, z][i], [x, y, z][j])).det())
H = hess(U)
HH = hess(H)
lam, mu = sp.symbols('lam mu')
eqs = sp.Poly(sp.expand(HH - lam*U - mu*H), x, y, z).coeffs()
sol = sp.solve(eqs[:3], [lam, mu], dict=True)
# solve() may pick two equations that are degenerate; use least-squares style: solve two, verify all
for cand in sp.solve([eqs[0], eqs[1]], [lam, mu], dict=True) + sol:
    if all(sp.simplify(q.subs(cand)) == 0 for q in eqs):
        L, M = sp.factor(cand[lam]), sp.factor(cand[mu]); break
print('lam =', L); print('mu =', M)
s4_0 = a*e**2*f + b*d*f**2 + c*d**2*e
s6_0 = 27*a**2*b**2*c**2 + 4*a**2*c*e**3 + 4*a*b**2*f**3 + 6*a*b*c*d*e*f + 4*b*c**2*d**3 - d**2*e**2*f**2
pickle.dump((L, M), open('hh.pkl', 'wb'))
print('lam(m=0) / s4_0^2 =', sp.cancel(L.subs(m, 0)/s4_0**2), '   mu(m=0) / s6_0 =', sp.cancel(M.subs(m, 0)/s6_0))
