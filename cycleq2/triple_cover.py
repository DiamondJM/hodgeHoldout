"""Triple base change of cycle-three's Jacobian model: (r:t) = (rho^3 : tau^3), tau/rho = v^2."""
import sympy as sp
from model_check import a8, b256
rho, tau, c1, c2, s = sp.symbols('rho tau c1 c2 s')
A1 = sp.Poly(sp.expand(a8(c1, c2, 1, 1, s)), s)      # cycle-three model, affine t/r = s = v^6
B1 = sp.Poly(sp.expand(b256(c1, c2, 1, 1, s)), s)
print('cycle-three model: deg_s a =', A1.degree(), ', deg_s b =', B1.degree(), ' -> (4,6): rational elliptic surface')
A3 = sp.expand(a8(c1, c2, 1, rho**3, tau**3)); B3 = sp.expand(b256(c1, c2, 1, rho**3, tau**3))
pa, pb = sp.Poly(A3, rho, tau), sp.Poly(B3, rho, tau)
print('triple cover: a is a form of degree', pa.total_degree(), ', b of degree', pb.total_degree())
for name, var in (('rho', rho), ('tau', tau)):
    oa = min(m[0 if var == rho else 1] for m in pa.monoms()); ob = min(m[0 if var == rho else 1] for m in pb.monoms())
    print(f'  order at {name}=0: ord(a) = {oa}, ord(b) = {ob}', '(reducible)' if oa >= 4 and ob >= 6 else '(minimal)')
# Non-isotriviality: j = 1728 * 4a^3/(4a^3+27b^2) in the normalisation y^2 = x^3 + (a8/8) x + b256/256
num = 4*(A1.as_expr()/8)**3; den = num + 27*(B1.as_expr()/256)**2
j = sp.cancel(num.subs({c1: 2, c2: 3})/den.subs({c1: 2, c2: 3}))
print('j-invariant (c1,c2)=(2,3) nonconstant in s:', sp.diff(j, s) != 0)
print('discriminant degree in s:', sp.Poly(sp.expand(den.subs({c1: 2, c2: 3})), s).degree())
