"""Step 2: is the transported q=2 source exact off fibres on the triple cover?
Solve G' + G/(3t) + M G = H for rational G (omega-sector, g = tau G(t), tau^3 = t)."""
import sympy as sp, pickle, sys
from gm import Fibre, t, xi
v, c1, c2 = sp.symbols('v c1 c2')
C1, C2 = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (2, 3)
D = pickle.load(open('variation.pkl', 'rb'))
def as_t(expr, vpow):
    e = sp.expand(sp.expand(expr.subs({c1: C1, c2: C2})) / v**vpow)
    e = sp.expand(e)
    assert all(sp.Poly(term, v).degree() % 6 == 0 for term in sp.Add.make_args(e)), (expr, vpow)
    return sp.expand(e.subs(v, t**sp.Rational(1, 6)))
a, b = as_t(D['A'], 0), as_t(D['B'], 0)
A1, B1, A2, B2, B12 = as_t(D['A1'], 3), as_t(D['B1'], 3), as_t(D['A2'], 2), as_t(D['B2'], 2), as_t(D['B12'], 5)
print('deg_t a, b =', sp.degree(a, t), sp.degree(b, t))
E = Fibre(a, b)
M = E.gauss_manin().applyfunc(sp.factor)
h5 = sp.Rational(3, 4)*(A1*xi + B1)*(A2*xi + B2)
r5 = E.reduce(h5, 5); r3 = E.reduce(-sp.Rational(1, 2)*B12, 3)
H = sp.Matrix([sp.factor(sp.together(r5[0] + r3[0])), sp.factor(sp.together(r5[1] + r3[1]))])
Delta = sp.factor(4*a**3 + 27*b**2)
print('Delta =', Delta)
print('den(M) =', [sp.factor(sp.denom(sp.together(x))) for x in M])
print('den(H) =', [sp.factor(sp.denom(x)) for x in H])
pickle.dump((C1, C2, a, b, M, H, Delta), open(f'step2_{C1}_{C2}.pkl', 'wb'))
