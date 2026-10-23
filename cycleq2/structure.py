"""cycle-q2: paired-ratio cubic, symmetry characters, and why holdout-q2's endpoint reduction has no analogue."""
import sympy as sp, itertools
X0,X1,X2,Y0,Y1,Y2,al,be,ga,U,V,W = sp.symbols('X0 X1 X2 Y0 Y1 Y2 alpha beta gamma U V W')
h = sp.Rational(1, 2)
F = sum(z**6 for z in (X0,X1,X2,Y0,Y1,Y2)) + h*X0**3*X1*Y0*Y1 + h*X0*X2**3*Y0*Y2 + h*X1**3*X2*Y1*Y2
A = X0**2*X1**2*X2**3*Y0**2*Y1**2*Y2
sub = {Y0: al*X0, Y1: be*X1, Y2: ga*X2}
Fc = sp.expand(F.subs(sub)); Ac = sp.expand(A.subs(sub))
Fc = sp.expand(Fc.subs({X0: sp.sqrt(U), X1: sp.sqrt(V), X2: sp.sqrt(W)}))
Ac = sp.expand(Ac.subs({X0: sp.sqrt(U), X1: sp.sqrt(V), X2: sp.sqrt(W)}))
print('F =', sp.collect(Fc, [U, V, W]))
print('A =', Ac)
J = sp.Matrix([[2*X0, 0], [-Y0/X0**2, 1/X0]]).det()
print('pair Jacobian d(X^2, Y/X) =', sp.simplify(J), '-> total 8')
# Diagonal symmetries of F modulo scalars; residue character of A*vol.
mons = [m for m in sp.Poly(F, X0,X1,X2,Y0,Y1,Y2).monoms()]
G = {tuple((g - g0) % 6 for g in gg) for gg in itertools.product(range(6), repeat=6)
     if all(sum(a*b for a, b in zip(gg, m)) % 6 == 0 for m in mons) for g0 in [gg[0]]}
eA = sp.Poly(A, X0,X1,X2,Y0,Y1,Y2).monoms()[0]
print('|G| mod scalars =', len(G))
for g in sorted(G):
    ch = (sum(a*b for a, b in zip(g, eA)) + sum(g)) % 6
    print(' g =', g, ' residue character of A: zeta^%d' % ch)
