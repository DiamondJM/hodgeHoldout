import sympy as sp
r,s,t,k,p,q,al,be = sp.symbols('r s t k p q alpha beta')
m = r**4-4*r**3+5*r**2+r-2
R = r*(1-r-r**2)/(1-r); M = r**2*m/(r-1)**2
a = 3*(1-2*r)/(1-r); b = 3*(1-2*r)
X0, X1, X2 = s**2, k*s*t, t**2
S = -(s**4+q**2*s**2*t**2+t**4); P = p*s**3*t+q*s*t**3
H = X0**6+X1**6+X2**6 + P*(al*X0**3*X1+be*X1**3*X2) + S**3-3*S*P**2
# relations: q^4=R, k^6=M/q^2, p=r/q, alpha=a/(k q), beta=b/(k^3 q)
Hs = sp.expand(H.subs({p: r/q, al: a/(k*q), be: b/(k**3*q)}))
Hs = sp.expand(Hs*q**4*k**4)  # clear denominators (check)
poly = sp.Poly(sp.expand(sp.cancel(Hs)), s, t)
# reduce each coefficient modulo q^4 = R and k^6 = M/q^2 : substitute k^6 -> M/q^2 then q^4 -> R
def reduce(e):
    e = sp.expand(e)
    e = e.subs(k**12, (M/q**2)**2).subs(k**6, M/q**2)
    e = sp.expand(e)
    for n in range(12, 3, -1):
        e = e.subs(q**n, R**(n//4)*q**(n%4))
    return sp.simplify(e)
bad = {mon: reduce(c) for mon, c in poly.terms() if reduce(c) != 0}
print("family identity residual monomials:", bad if bad else "none -> conic lies on H(alpha_c,beta_c) for every r")
# one-reflection condition beta = alpha  <=>  k^2 = b/a = 1-r ; with k^6 = M/q^2 and q^4 = R
g = sp.expand(r**3*m**2 - (1-r-r**2)*(1-r)**9)
print("beta=alpha polynomial g(r) =", sp.factor(g))
roots = sp.Poly(g, r).nroots(n=30)
print("roots:", roots)
geven = 16*r**11-80*r**10+96*r**9+144*r**8-380*r**7+240*r**6+84*r**5-178*r**4+63*r**3+9*r**2-8*r+1
godd = 8*r**11-48*r**10+112*r**9-16*r**8-224*r**7+352*r**6-275*r**5+101*r**4+11*r**3-24*r**2+8*r-1
print("gcd(g, g_even) =", sp.gcd(g, geven), " gcd(g, g_odd) =", sp.gcd(g, godd))
print("gcd(g, m) =", sp.gcd(g, m), " gcd(g, 1-2r) =", sp.gcd(g, 1-2*r), " g(0),g(1) =", g.subs(r,0), g.subs(r,1))
