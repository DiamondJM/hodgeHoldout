"""Anchored conic incidence system for the deformed quotient
H' = f(X) + P(alpha X0^3 X1 + beta X1^3 X2) + S^3 - 3 S P^2,
f = X0^6+X1^6+X2^6 + (X0^5 X1 + 2 X1^5 X2 + X2^5 X0)/14,
at the endpoint (1,0,0,-1,0) with X1 = k*tau, chart s=1."""
import sympy as sp, sys
tau = sp.symbols('tau')
a1,a2,c1,c2 = sp.symbols('a1 a2 c1 c2')
d = sp.symbols('d1:5'); e = sp.symbols('e1:5')
alpha, beta, k = sp.Rational(1), sp.Rational(0), sp.Rational(1)
if len(sys.argv) > 1: k = sp.Rational(sys.argv[1])
if len(sys.argv) > 3: alpha, beta = sp.Rational(sys.argv[2]), sp.Rational(sys.argv[3])
X0 = 1 + a1*tau + a2*tau**2
X1 = k*tau
X2 = c1*tau + c2*tau**2
S = -1 + sum(d[i]*tau**(i+1) for i in range(4))
P = sum(e[i]*tau**(i+1) for i in range(4))
f = X0**6 + X1**6 + X2**6 + (X0**5*X1 + 2*X1**5*X2 + X2**5*X0)/14
H = f + P*(alpha*X0**3*X1 + beta*X1**3*X2) + S**3 - 3*S*P**2
Hp = sp.Poly(sp.expand(14*H), tau)
coeffs = {m[0]: c for m, c in Hp.terms()}
eqs = [sp.expand(coeffs.get(n, 0)) for n in range(1, 13)]
assert sp.expand(coeffs.get(0, 0)) == 0
vars_ = [a1,a2,c1,c2,*d,*e]
with open('sys.ms','w') as fh:
    fh.write(','.join(map(str,vars_))+'\n0\n')
    fh.write(',\n'.join(str(eq).replace('**','^') for eq in eqs)+'\n')
print("degrees:", [sp.Poly(eq, *vars_).total_degree() for eq in eqs])
