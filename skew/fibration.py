"""Fibration of one-reflection(-skew) over passive ratios r=X1/X0, w=X2/X0, x=Y0/Y1:
the fibre is the plane sextic g(X0^2, Y1^2) + Y2^6 = 0 with g a binary cubic, and the
residue character of A = X0^3 Y0^3 picks a 2-dimensional, purely (1,0) eigenspace of H^1(fibre)."""
import sympy as sp, itertools
X0,X1,X2,Y0,Y1,Y2,r,w,x,U,V = sp.symbols('X0 X1 X2 Y0 Y1 Y2 r w x U V')
F0 = sum(v**6 for v in (X0,X1,X2,Y0,Y1,Y2)) + X0**3*X1*Y0*Y1 + X1**3*X2*Y0*Y1
K = X0*X1*Y0*Y1*(Y0**2-Y1**2)
for name, F in (('one-reflection', F0), ('one-reflection-skew', F0 + K/7)):
    fib = sp.expand(F.subs({X1: r*X0, X2: w*X0, Y0: x*Y1}))
    g = sp.expand((fib - Y2**6).subs({X0: sp.sqrt(U), Y1: sp.sqrt(V)}))
    assert all(sp.degree(t, U) + sp.degree(t, V) == 3 for t in sp.Add.make_args(g)), name
    print(name, ': fibre = g(X0^2,Y1^2) + Y2^6,  g =', sp.factor_terms(sp.collect(g, [U, V])))
# Residue character of A*vol under the fibrewise group (X-block sign, (Y0,Y1) sign, Y2 -> zeta Y2):
# A = X0^3 Y0^3: X-sign -> (-1)*(det -1) = +1 ; (Y0,Y1)-sign -> (-1)*(det +1) = -1 ; Y2 -> zeta.
# Fibre 1-forms Res(P Omega / G), deg P = 3 in (X0, Y1, Y2), carry the character of P*X0*Y1*Y2.
h10 = [(a, b, 3-a-b) for a in range(4) for b in range(4-a)
       if (a+1) % 2 == 0 and (b+1) % 2 == 1 and (3-a-b+1) % 6 == 1]
h01 = [(a, b, 3-a-b) for a in range(4) for b in range(4-a)            # conj: Y2 char zeta^5
       if (a+1) % 2 == 0 and (b+1) % 2 == 1 and (3-a-b+1) % 6 == 5]
print('chi-eigenspace H^{1,0}: P =', ['X0^%d Y1^%d Y2^%d' % m for m in h10], ' H^{0,1} dim =', len(h01))
