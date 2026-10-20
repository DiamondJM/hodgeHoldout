import sympy as sp
tau = sp.symbols('tau')
a1,a2,c1,c2 = sp.symbols('a1 a2 c1 c2')
d = list(sp.symbols('d1:5')); e = list(sp.symbols('e1:5'))
alpha, beta, k = 1, 0, 1
X0 = 1 + a1*tau + a2*tau**2; X1 = k*tau; X2 = c1*tau + c2*tau**2
S = -1 + sum(d[i]*tau**(i+1) for i in range(4)); P = sum(e[i]*tau**(i+1) for i in range(4))
f = X0**6 + X1**6 + X2**6 + sp.Rational(1,14)*(X0**5*X1 + 2*X1**5*X2 + X2**5*X0)
H = f + P*(alpha*X0**3*X1 + beta*X1**3*X2) + S**3 - 3*S*P**2
Hp = sp.Poly(sp.expand(H), tau); co = {m[0]: c for m, c in Hp.terms()}
eqs = [sp.expand(co.get(n, 0)) for n in range(1, 13)]
# eliminate d1..d4 from equations tau^1..tau^4 (linear in d_n with coefficient 3)
sol = {}
for n in range(4):
    eq = sp.expand(eqs[n].subs(sol))
    dn = sp.solve(eq, d[n])[0]
    sol[d[n]] = sp.expand(dn)
rest = [sp.expand(eqs[n].subs(sol)) for n in range(4, 12)]
vars8 = [a1,a2,c1,c2,*e]
print("degrees:", [sp.Poly(r, *vars8).total_degree() for r in rest], "terms:", [len(sp.Poly(r,*vars8).terms()) for r in rest])
# integer-clear
import math
def clear(expr):
    P_ = sp.Poly(expr, *vars8)
    den = sp.ilcm(*[sp.Rational(c).q for c in P_.coeffs()])
    return sp.expand(expr*den)
rest = [clear(r) for r in rest]
for p in (65521, 0):
    with open(f'sys8_{p}.ms','w') as fh:
        fh.write(','.join(map(str,vars8))+f'\n{p}\n')
        fh.write(',\n'.join(str(r).replace('**','^') for r in rest)+'\n')
print("written")
