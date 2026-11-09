"""four-plus-two-residual reduced to the 4-variable core: find rational p = N/D (deg N_i = deg D + 1) with
      p(H) - (3/2) H div p = A,   i.e.   D N(H) - (3/2) H (D div N - N(D)) = A D^2.
Fixed D makes this linear in N.  Exact over Q or mod p."""
import itertools, sys
from flint import fmpq_mpoly_ctx, fmpq, nmod_mat
P = 268435399
ctx = fmpq_mpoly_ctx.get(('X0', 'X1', 'Y0', 'Y1'))
X0, X1, Y0, Y1 = V = ctx.gens()
q = lambda a, b=1: fmpq(a, b)
hX = X0**6 + q(5, 7)*X0**5*X1 + q(10, 7)*X0*X1**5 + X1**6
hY = Y0**6 + q(5, 7)*Y0**5*Y1 + q(15, 7)*Y0*Y1**5 + Y1**6
CPL = q(5, 7)*X0**3*X1*Y0*Y1 + q(10, 7)*X0*X1*Y0**3*Y1
H = hX + hY + CPL
A = X0**3*Y0**3

def monos(n):
    return [e for e in itertools.product(range(n + 1), repeat=4) if sum(e) == n]
def modp(c):
    c = fmpq(c); return int(c.p) * pow(int(c.q), -1, P) % P

def solvable(Hh, Aa, D):
    d = D.total_degree()
    J = [Hh.derivative(i) for i in range(4)]; dD = [D.derivative(i) for i in range(4)]
    cols = []
    for i in range(4):
        for e in monos(d + 1):
            m = ctx.from_dict({e: 1})
            cols.append(D*m*J[i] - q(3, 2)*Hh*(D*m.derivative(i) - m*dD[i]))
    rhs = Aa*D*D
    rows = {}
    for p in cols + [rhs]:
        for m in p.monoms(): rows.setdefault(m, len(rows))
    M = nmod_mat(len(rows), len(cols) + 1, P)
    for j, p in enumerate(cols + [rhs]):
        for m, c in zip(p.monoms(), p.coeffs()): M[rows[m], j] = modp(c)
    M0 = nmod_mat(len(rows), len(cols), P)
    for j, p in enumerate(cols):
        for m, c in zip(p.monoms(), p.coeffs()): M0[rows[m], j] = modp(c)
    r0 = M0.rank()
    return r0 == M.rank(), len(cols), r0

if __name__ == '__main__':
    Hs = hX + hY
    print('control  split core, A = X0^3 X1 Y0^2 (X-degree 4), D = hX :', solvable(Hs, X0**3*X1*Y0**2, hX)[0], '(expect True)')
    print('control  split core, A = X0^3 Y0^3   (X-degree 3), D = hX :', solvable(Hs, X0**3*Y0**3, hX)[0], '(expect False)')
    print('control  split core, A = X0^3 Y0^3, D = hY               :', solvable(Hs, X0**3*Y0**3, hY)[0], '(expect False)')
