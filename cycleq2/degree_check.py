import sympy as sp, pickle
from gm import t, xi
v, c1, c2, tau = sp.symbols('v c1 c2 tau')
D = pickle.load(open('variation.pkl', 'rb'))
C1, C2 = 2, 3
def as_t(expr, vpow):
    e = sp.expand(sp.expand(expr.subs({c1: C1, c2: C2})) / v**vpow)
    return sp.expand(e.subs(v, t**sp.Rational(1, 6)))
q = {k: as_t(D[k], p) for k, p in (('A',0),('B',0),('A1',3),('B1',3),('A2',2),('B2',2),('B12',5))}
for k, e in q.items(): print(k, 'deg_t =', sp.degree(e, t))
# P (cubic-pole numerator) in the chart rho=1, tau: t = tau^3, v^2 = tau, dt = 3 tau^2 dtau
P = sp.expand((3*tau**3) * sp.Rational(3,4) * ((q['A1']*xi + q['B1'])*(q['A2']*xi + q['B2'])).subs(t, tau**3))
wdeg = max(sp.Poly(m, tau, xi).monoms()[0][0] + 6*sp.Poly(m, tau, xi).monoms()[0][1] for m in sp.Add.make_args(P))
print('weighted degree of P (tau:1, xi:6) =', wdeg, ' (must be <= 37 for no pole along the fibre at infinity)')
