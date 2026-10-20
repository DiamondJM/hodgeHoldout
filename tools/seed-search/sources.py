"""Check the quotient source and deck-eigenvalue data of fqlx's holdout cover for every
degree-6 Y-odd monomial target on the holdout sextic (and the ten open targets in particular)."""
import sympy as sp
X0,X1,X2,Y0,Y1,Y2 = Z = sp.symbols('X0 X1 X2 Y0 Y1 Y2')
al,be,T,y,S,P = sp.symbols('alpha beta T y S P')
F = X0**6+X1**6+X2**6+Y0**6+Y1**6+Y2**6 + X0**3*X1*Y0*Y1 + X1**3*X2*Y1*Y2
# cover: Y0 = alpha T, Y1 = y, Y2 = beta T,  alpha^6+beta^6 = 1
cov = {Y0: al*T, Y1: y, Y2: be*T}
G = sp.expand(F.subs(cov))
Gexp = X0**6+X1**6+X2**6+y**6+T**6*(al**6+be**6) + y*T*(al*X0**3*X1+be*X1**3*X2)
assert sp.expand(G-Gexp)==0
H = X0**6+X1**6+X2**6 + P*(al*X0**3*X1+be*X1**3*X2) + S**3-3*S*P**2
assert sp.expand(H.subs({S:y**2+T**2, P:y*T}) - (Gexp.subs(al**6, 1-be**6))) == 0  # with alpha^6+beta^6=1
# Jacobian of (Y0,Y1,Y2) wrt (y,T,beta) with alpha = (1-beta^6)^(1/6): d alpha/d beta = -beta^5/alpha^5
dal = -be**5/al**5
Jac = sp.Matrix([[0, al, T*dal],[1,0,0],[0,be,T]]).det()
Jac = sp.simplify(Jac.subs(be**6, 1-al**6)); assert sp.simplify(Jac + T/al**5) == 0, Jac
JSP = sp.Matrix([[2*y,2*T],[T,y]]).det()   # d(S,P)/d(y,T) = 2(y^2-T^2)
def analyse(A):
    dens = sp.expand(A.subs(cov)*Jac)                     # pulled-back density
    refl = sp.expand(dens.subs({y:T, T:y}, simultaneous=True)*(-1))  # reflected pullback (det -1)
    tot = sp.expand(dens + refl)
    Bq = sp.cancel(tot/JSP)                                  # quotient source in y,T
    # express in S,P: Bq must be symmetric in y,T
    B = sp.simplify(Bq)
    # convert symmetric polynomial in y,T to S,P
    Bp = sp.Poly(sp.expand(B*al**5*be**0), y, T)
    deg = Bp.total_degree()
    cs = []; expr = 0
    for i in range(deg//2+1):
        for j in range(deg//2+1-i):
            c = sp.Symbol(f'c_{i}_{j}'); cs.append(c); expr += c*S**i*P**j
    diff = sp.Poly(sp.expand(expr.subs({S:y**2+T**2, P:y*T}) - B*al**5), y, T)
    sol = sp.solve(diff.coeffs(), cs, dict=True)
    assert sol, (A, B)
    Bfin = sp.expand(expr.subs(sol[0]).subs({c:0 for c in cs})/al**5)
    # companion: ratio refl/dens
    ratio = sp.cancel(refl/dens)
    k = sp.degree(sp.numer(ratio), y) - sp.degree(sp.denom(ratio), y)
    # eigenvalue of companion A*(y/T)^k under T->zT (physical fixed): z^{-k}; ok iff k mod 6 != 0
    return Bfin, sp.simplify(ratio), k
targets = {
 'holdout (solved)':X0**3*Y0**3, 'holdout-x13-y13':X1**3*Y1**3, 'holdout-p3':X2**3*Y2**3,
 'holdout-x12-p-y02':X1**2*X2*Y0**2*Y2, 'holdout-p-y14':X2*Y1**4*Y2, 'holdout-x1-y04-y1':X1*Y0**4*Y1,
 'holdout-x0-y03-y12':X0*Y0**3*Y1**2, 'holdout-all-six':X0*X1*X2*Y0*Y1*Y2, 'holdout-x0-x14-y0':X0*X1**4*Y0,
 'holdout-x04-p':X0**4*X2*Y2, 'bundle 2nd term':X0**3*Y0*Y1**2}
for name,A in targets.items():
    B,ratio,k = analyse(A)
    wt = sp.Poly(B.subs({S:S,P:P}), X0,X1,X2,S,P)
    w = {m: sum(e*wt_ for e,wt_ in zip(m,(1,1,1,2,2))) for m in wt.monoms()}
    print(f"{name:22s} A={A}  B={B}  companion ratio={ratio}  k={k}  weights={set(w.values())}  deck_ok={k%6!=0}")
