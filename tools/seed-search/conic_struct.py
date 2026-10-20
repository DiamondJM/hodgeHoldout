import sympy as sp
s,t = sp.symbols('s t')
k1,k2,al,be = sp.symbols('k1 k2 alpha beta')
d = list(sp.symbols('d1:4')); e = list(sp.symbols('e0:5'))
X0 = s**2; X1 = k1*s*t + k2*t**2; X2 = t**2
S = -s**4 + d[0]*s**3*t + d[1]*s**2*t**2 + d[2]*s*t**3 - t**4
P = sum(e[i]*s**(4-i)*t**i for i in range(5))
f = X0**6 + X1**6 + X2**6 + sp.Rational(1,14)*(X0**5*X1 + 2*X1**5*X2 + X2**5*X0)
H = sp.expand(14*(f + P*(al*X0**3*X1 + be*X1**3*X2) + S**3 - 3*S*P**2))
Hp = sp.Poly(H, s, t)
eqs = [sp.expand(Hp.coeff_monomial(s**(12-i)*t**i)) for i in range(13)]
pass
eqs = [q for q in eqs if q != 0] + [al**6 + be**6 - 1]
vars_ = [k1,k2,*d,*e,al,be]
print(len(eqs), "equations,", len(vars_), "unknowns; degrees", [sp.Poly(q, *vars_).total_degree() for q in eqs])
with open('struct_p.ms','w') as fh:
    fh.write(','.join(map(str,vars_))+'\n65521\n'); fh.write(',\n'.join(str(q).replace('**','^') for q in eqs)+'\n')
