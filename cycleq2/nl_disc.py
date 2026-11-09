"""Noether-Lefschetz candidates for cycle-q2: base curves in the (c1,c2)-plane where cycle-three's
Weierstrass fibration eta^2 = xi^3 + a(t) xi + b(t) has colliding singular fibres."""
import sympy as sp, pickle, subprocess, sys
v, c1, c2, t = sp.symbols('v c1 c2 t')
D = pickle.load(open('variation.pkl', 'rb'))
def as_t(expr): return sp.expand(sp.expand(expr).subs(v, t**sp.Rational(1, 6)))
a, b = as_t(D['A']), as_t(D['B'])
a, b = sp.factor(a), sp.factor(b)
print('a =', a); print('deg_t b =', sp.degree(sp.expand(b), t))
Delta = sp.expand(4*sp.expand(a)**3 + 27*sp.expand(b)**2)
Df = sp.factor(Delta)
print('Delta factors:', [ (sp.degree(f, t), m) for f, m in sp.factor_list(Delta)[1]])
pickle.dump((sp.expand(a), sp.expand(b), Delta), open('abDelta.pkl', 'wb'))
