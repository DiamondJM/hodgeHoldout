"""Step 1: a norm-contact presentation of T: H(a,b,c,d) + u^3 = 0 (book 3B.2) after eliminating u = q(x):
      H + q^3 = h * sigma(h) + Q * M
with q, Q sigma-even quadrics, h a cubic, M a sigma-even quartic, sigma: (c,d) -> (-c,-d).
Then C = {u = q, Q = 0, h = 0} and sigma(C) are genus-4 curves on T with C + sigma C = T ∩ {u = q, Q = 0}.
Gauge: Q[a^2] = 1, q[a^2] = 0, h has no monomial divisible by a^2, q[ab] = t0 (family parameter)."""
import sympy as sp, numpy as np, itertools, pickle, sys, time
a, b, c, d = X = sp.symbols('a b c d')
R = sp.Rational
H = (a**6 + R(5,7)*a**5*b + R(10,7)*a*b**5 + b**6 + c**6 + R(5,7)*c**5*d + R(15,7)*c*d**5 + d**6
     + R(5,7)*a**3*b*c*d + R(10,7)*a*b*c**3*d)
def monos(n, parity=None):
    out = []
    for e in itertools.product(range(n+1), repeat=4):
        if sum(e) == n and (parity is None or (e[2]+e[3]) % 2 == parity): out.append(e)
    return out
mono = lambda e: a**e[0]*b**e[1]*c**e[2]*d**e[3]
E2, E4, E6 = monos(2, 0), monos(4, 0), monos(6, 0)
C3 = monos(3)
qs = sp.symbols('q0:%d' % len(E2)); Qs = sp.symbols('Q0:%d' % len(E2))
hs = sp.symbols('h0:%d' % len(C3)); Ms = sp.symbols('M0:%d' % len(E4))
t0 = sp.Symbol('t0')
subs_g = {Qs[E2.index((2,0,0,0))]: 1, qs[E2.index((2,0,0,0))]: 0, qs[E2.index((1,1,0,0))]: t0}
subs_g.update({hs[i]: 0 for i, e in enumerate(C3) if e[0] >= 2})
q = sum(s*mono(e) for s, e in zip(qs, E2)).subs(subs_g)
Q = sum(s*mono(e) for s, e in zip(Qs, E2)).subs(subs_g)
h = sum(s*mono(e) for s, e in zip(hs, C3)).subs(subs_g)
M = sum(s*mono(e) for s, e in zip(Ms, E4))
sh = h.subs({c: -c, d: -d}, simultaneous=True)
expr = sp.expand(H + q**3 - h*sh - Q*M)
P = sp.Poly(expr, a, b, c, d)
eqs = [P.coeff_monomial(mono(e)) for e in E6]
unk = [s for s in list(qs) + list(Qs) + list(hs) + list(Ms) if s not in subs_g]
assert all(P.coeff_monomial(mono(e)) == 0 for e in monos(6, 1))
print(len(eqs), 'equations,', len(unk), 'unknowns')
Jsym = sp.Matrix(eqs).jacobian(unk)
f_res = sp.lambdify([unk, t0], eqs, 'numpy'); f_jac = sp.lambdify([unk, t0], Jsym, 'numpy')
pickle.dump((eqs, unk, subs_g, E2, E4, C3), open('nc_system.pkl', 'wb'))

def newton(x, tv, iters=200):
    for it in range(iters):
        r = np.array(f_res(x, tv), dtype=complex)
        nr = np.linalg.norm(r)
        if nr < 1e-13: return x, nr, it
        J = np.array(f_jac(x, tv), dtype=complex)
        dx = np.linalg.lstsq(J, -r, rcond=None)[0]
        lam = 1.0
        while lam > 1e-4:
            xn = x + lam*dx
            if np.linalg.norm(np.array(f_res(xn, tv), dtype=complex)) < (1 - 0.3*lam)*nr: break
            lam /= 2
        x = x + lam*dx
    return x, np.linalg.norm(np.array(f_res(x, tv), dtype=complex)), iters

if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    tv = 0.37 + 0.21j
    sols = []; t_start = time.time()
    for trial in range(int(sys.argv[2]) if len(sys.argv) > 2 else 60):
        x0 = (rng.normal(size=len(unk)) + 1j*rng.normal(size=len(unk)))
        x, nr, it = newton(x0, tv)
        if nr < 1e-11:
            J = np.array(f_jac(x, tv), dtype=complex)
            sv = np.linalg.svd(J, compute_uv=False)
            new = all(np.linalg.norm(x - y) > 1e-6 for y in sols)
            if new: sols.append(x)
            print(f'trial {trial}: converged, residual {nr:.1e}, iters {it}, smallest singular value {sv[-1]:.2e}, new={new}', flush=True)
    print(f'{len(sols)} distinct solutions in {time.time()-t_start:.0f}s')
    np.save('nc_solutions.npy', np.array(sols)) if sols else None
