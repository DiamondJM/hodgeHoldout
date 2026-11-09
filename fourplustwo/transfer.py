"""Suspension transfer for F = H(x) + B(s,t), deg B = 6:  a field on (x, w)-space
   V = sum_i P_i(x, w^3) d/dx_i + R(x, w^3) w d/dw     (G = H + w^3)
transfers to  V' = sum_i P_i(x, B) d/dx_i + R(x, B) (s d/ds + t d/dt)/2  with
   V'(F) = V(G)|_{w^3=B},  div V' = (div V)|_{w^3=B}.  Symbolic check with random rational P_i, R."""
import sympy as sp, random
x0, x1, y0, y1, w, s, t, z = sp.symbols('x0 x1 y0 y1 w s t z')
X = (x0, x1, y0, y1)
random.seed(5)
def rnd_poly(deg_x, deg_z):
    return sum(random.randint(-3, 3)*x0**a*x1**b*y0**c*y1**d*z**e
               for a in range(deg_x+1) for b in range(deg_x+1-a) for c in range(2) for d in range(2) for e in range(deg_z+1))
H = sum(random.randint(1, 5)*m for m in (x0**6, x1**6, y0**6, y1**6, x0**3*x1*y0*y1, x0*x1*y0**3*y1, x0**5*x1))
B = s**6 + sp.Rational(15, 7)*s**4*t**2 + sp.Rational(10, 7)*s**2*t**4 + t**6
P = [rnd_poly(2, 1)/(1 + rnd_poly(1, 1)) for _ in range(4)]
R = rnd_poly(1, 1)/(2 + rnd_poly(1, 1))
G = H + w**3
up = lambda e: e.subs(z, w**3)
VG = sum(up(P[i])*sp.diff(G, X[i]) for i in range(4)) + up(R)*w*sp.diff(G, w)
divV = sum(sp.diff(up(P[i]), X[i]) for i in range(4)) + sp.diff(up(R)*w, w)
F = H + B
dn = lambda e: e.subs(z, B)
VF = sum(dn(P[i])*sp.diff(F, X[i]) for i in range(4)) + dn(R)*(s*sp.diff(F, s) + t*sp.diff(F, t))/2
divVp = sum(sp.diff(dn(P[i]), X[i]) for i in range(4)) + (sp.diff(dn(R)*s, s) + sp.diff(dn(R)*t, t))/2
# compare after substituting w^3 -> B: write both sides in z
pts = [{x0: sp.Rational(random.randint(1, 9), random.randint(1, 5)), x1: sp.Rational(random.randint(1, 9), 7),
        y0: sp.Rational(random.randint(1, 9), 3), y1: sp.Rational(random.randint(1, 9), 11),
        s: sp.Rational(random.randint(1, 9), 2), t: sp.Rational(random.randint(1, 9), 13)} for _ in range(5)]
ok1 = ok2 = True
for pt in pts:
    Bv = B.subs(pt)
    xs = {k: v for k, v in pt.items() if k in X}
    # left side: differentiate in (x, w), then put w^3 = B.  Every term is a function of w^3 only.
    lhs1 = sp.nsimplify(VG.subs(xs).subs(w, sp.Symbol('W', positive=True)))
    W = sp.Symbol('W', positive=True)
    f1 = sp.cancel(sp.simplify(VG.subs(xs).subs(w, W)).subs(W**3, z)) if False else None
    val1 = sp.simplify(sp.cancel(VG.subs(xs)).subs(w, sp.root(Bv, 3)))
    val2 = sp.simplify(sp.cancel(divV.subs(xs)).subs(w, sp.root(Bv, 3)))
    ok1 &= sp.simplify(val1 - VF.subs(pt)) == 0
    ok2 &= sp.simplify(val2 - divVp.subs(pt)) == 0
print('V(F) matches at 5 random rational points:', ok1)
print('div  matches at 5 random rational points:', ok2)
