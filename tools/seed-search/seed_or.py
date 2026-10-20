import sympy as sp
r = sp.symbols('r')
m = r**4-4*r**3+5*r**2+r-2
R = r*(1-r-r**2)/(1-r); M = r**2*m/(r-1)**2
a = 3*(1-2*r)/(1-r); b = 3*(1-2*r)
graw = sp.expand(r**3*m**2 - (1-r-r**2)*(1-r)**9)
print("graw factored:", sp.factor(graw))
g = sp.Poly(sp.factor_list(graw)[1][-1][0], r)
print("g =", g.as_expr(), " degree", g.degree())
# which factor; check all factors
for fac, mult in sp.factor_list(graw)[1]:
    print("factor", fac, "roots", sp.Poly(fac, r).nroots(n=12))
gE = sp.Poly(16*r**11-80*r**10+96*r**9+144*r**8-380*r**7+240*r**6+84*r**5-178*r**4+63*r**3+9*r**2-8*r+1, r)
gO = sp.Poly(8*r**11-48*r**10+112*r**9-16*r**8-224*r**7+352*r**6-275*r**5+101*r**4+11*r**3-24*r**2+8*r-1, r)
for name, h in (("gEven", gE), ("gOdd", gO), ("m", sp.Poly(m, r)), ("1-2r", sp.Poly(1-2*r, r)), ("1-r-r^2", sp.Poly(1-r-r**2, r))):
    s, t, d = sp.gcdex(g, h)  # s*g + t*h = d
    assert d.degree() == 0
    s, t = s * (1/d.LC()), t * (1/d.LC())
    print(f"Bezout {name}: deg s={s.degree()} deg t={t.degree()}; max denominator digits",
          max(len(str(c.q)) for c in list(s.all_coeffs())+list(t.all_coeffs())))
print("g(-13) =", g.eval(-13), " g(-12) =", g.eval(-12), " g(0)=", g.eval(0), " g(1)=", g.eval(1))
# sign-definiteness of gEven, gOdd, m, 1-r-r^2 on (-13,-12): shift r = -13 + u, u in (0,1)
u = sp.symbols('u')
for name, h in (("gEven", gE.as_expr()), ("gOdd", gO.as_expr()), ("m", m), ("1-r-r^2", 1-r-r**2), ("g", g.as_expr())):
    hu = sp.Poly(sp.expand(h.subs(r, -13+u)), u)
    cs = hu.all_coeffs()
    print(name, "shifted coeff signs:", ''.join('+' if c>0 else '-' if c<0 else '0' for c in cs), " value at r=-12.62:", sp.N(h.subs(r, -12.623), 6))
