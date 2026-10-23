"""Pole-two transport for cycle-q2, cohomological form.
2 A2 Omega/F^3 = d_s1 d_s2 (Omega/F_s), F_s = F + s1 X0X1X2Y0Y1Y2 + s2 X0X1X2^2Y0Y1: both add an xyz term
to cycle-three's cubic, with coefficients g1 = v^3 c1 c2, g2 = v^2 c1.  We compute the variations of the
Weierstrass coefficients A = s4, B = -s6/4 and the v-exponents (mod 6) of every term."""
import sympy as sp
from inv_check import s4 as s4_48, s6 as s6_216
v, c1, c2, s1, s2 = sp.symbols('v c1 c2 s1 s2')
co = dict(a=1+v**6, b=1+c1**6*v**6, c=1+c2**6*v**6, d=v**2*c1/2, e=v**2*c1*c2/2, f=v**2*c2/2)
mm = s1*v**3*c1*c2 + s2*v**2*c1
A = s4_48(co['a'],co['b'],co['c'],co['d'],co['e'],co['f'],mm)/48
B = -s6_216(co['a'],co['b'],co['c'],co['d'],co['e'],co['f'],mm)/864
def at0(expr): return sp.expand(expr.subs({s1: 0, s2: 0}))
data = {'A': at0(A), 'B': at0(B),
        'A1': at0(sp.diff(A, s1)), 'B1': at0(sp.diff(B, s1)),
        'A2': at0(sp.diff(A, s2)), 'B2': at0(sp.diff(B, s2)),
        'A12': at0(sp.diff(A, s1, s2)), 'B12': at0(sp.diff(B, s1, s2))}
for k, ex in data.items():
    exps = sorted({sp.Poly(t, v).degree() % 6 for t in sp.Add.make_args(ex)}) if ex != 0 else '-'
    print(f'{k:4}: v-exponents mod 6 = {exps}')
# weights: A, B have v-exponent 0 mod 6 (functions of t = v^6 on M1); the q=2 source
#   S = h^{-1} [ 3 (A1 xi + B1)(A2 xi + B2) / (4 eta^5) - (A12 xi + B12)/(2 eta^3) ] d(model)
# with h = -144 R v^3 (cycle-three density_multiplier) has v-exponent 3 + 2 - 3 = 2 = 5 - 3 mod 6.
import pickle; pickle.dump(data, open('variation.pkl', 'wb'))
