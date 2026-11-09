"""Restrict to a line c2 = const: factor disc_t(Delta) and Res_t(a, b) as polynomials in c1."""
import sympy as sp, pickle, sys
c1, c2, t = sp.symbols('c1 c2 t')
a, b, Delta = pickle.load(open('abDelta.pkl', 'rb'))
C2 = sp.Rational(sys.argv[1]) if len(sys.argv) > 1 else sp.Integer(3)
aL, bL, DL = [sp.Poly(sp.expand(e.subs(c2, C2)), t, c1, domain='QQ') for e in (a, b, Delta)]
disc = sp.Poly(sp.resultant(DL.as_expr(), sp.diff(DL.as_expr(), t), t), c1, domain='QQ')
print('deg disc_t(Delta) in c1:', disc.degree())
res_ab = sp.Poly(sp.resultant(aL.as_expr(), bL.as_expr(), t), c1, domain='QQ')
lead = sp.Poly(sp.Poly(DL.as_expr(), t).LC(), c1, domain='QQ')
const = sp.Poly(sp.Poly(DL.as_expr(), t).TC(), c1, domain='QQ')
def show(name, P):
    fl = sp.factor_list(P.as_expr())[1]
    print(name, ':', sorted([(sp.degree(f, c1), m) for f, m in fl]))
    return fl
fd = show('disc factors (deg, mult)', disc)
fr = show('Res(a,b) factors', res_ab)
show('lc_t(Delta)', lead); show('Delta(t=0)', const)
resfac = {sp.Poly(f, c1).monic() for f, m in fr}
print('disc factors NOT from cusps (a=b=0):')
for f, m in fd:
    if sp.Poly(f, c1).monic() not in resfac:
        print('   degree', sp.degree(f, c1), 'mult', m, ' ', f if sp.degree(f, c1) <= 8 else '')
pickle.dump([(f, m) for f, m in fd], open('disc_line_%s.pkl' % str(C2).replace('/', '_'), 'wb'))
