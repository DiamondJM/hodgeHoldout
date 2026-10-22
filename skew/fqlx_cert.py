"""fqlx's strict half-certificate for one-reflection (data/one-reflection/solution.md, section 4), mod p."""
from flint import nmod_mpoly_ctx, nmod
P = 268435009  # prime with sqrt(3) mod P
ctx = nmod_mpoly_ctx.get(('X0','X1','X2','Y0','Y1','Y2'), modulus=P)
X0,X1,X2,Y0,Y1,Y2 = ctx.gens()
V = ctx.gens()

def sqrt_mod(a, p):
    # Tonelli-Shanks
    q, s = p - 1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while pow(z, (p-1)//2, p) != p-1: z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q+1)//2, p)
    while t != 1:
        i, tt = 0, t
        while tt != 1: tt = tt*tt % p; i += 1
        b = pow(c, 1 << (m-i-1), p); m, c, t, r = i, b*b % p, t*b*b % p, r*b % p
    return r

lam = sqrt_mod(3, P); assert lam*lam % P == 3
inv = lambda a: pow(a, P-2, P)
def k(a, b=1): return a * inv(b) % P   # scalar a/b mod P

p_ = Y0*Y1; s = Y0**3 - Y1**3; S = Y0**3 + Y1**3; T = Y2**3
G0 = X0**6 + X1**6 + X2**6; c = X0**3*X1 + X1**3*X2
delta = 324*G0**2 + 24*c**3
h = -c**2 + 18*G0*p_ + 6*c*p_**2
f = G0 + c*p_ + 2*p_**3
R = T + k(lam, 3)*s
W = R**3 + f*T
Z = R**3*(R**3 + 2*f*T)
Dp = 9*delta*Z + 4*h**3*T**2
p0 = G0*c + 12*G0*p_**2 + k(1,3)*c**2*p_ + 6*c*p_**3
p1 = -3*G0*p_ + k(1,3)*c**2 + c*p_**2 + 6*p_**4
U = 81*G0*Z - 3*c*h*W*T + 3*h*p0*T**2
Vv = 9*c**2*Z - 3*c*h*W*p_*T + c*h*p1*T**2
B = -3*c*h*W*R
Np = [X0**3*e for e in (3*S*X0*U, 3*S*X1*U, 3*S*X2*U,
                         6*Y1**2*Vv + Y0*(s + 2*lam*T)*B,
                         6*Y0**2*Vv - Y1*(s + 2*lam*T)*B,
                         3*S*Y2*B)]
F0 = sum(v**6 for v in V) + X0**3*X1*Y0*Y1 + X1**3*X2*Y0*Y1
Kskew = X0*X1*Y0*Y1*(Y0**2 - Y1**2)
Ap = k(1, 2)*X0**3*S

def apply(N, g): return sum((N[i]*g.derivative(i) for i in range(6)), ctx.from_dict({}))
def div(N): return sum((N[i].derivative(i) for i in range(6)), ctx.from_dict({}))

if __name__ == '__main__':
    print('terms: D+', len(Dp), ' N+', [len(n) for n in Np])
    print('N+(F0) == A+ D+ :', apply(Np, F0) == Ap*Dp)
    print('D+ div N+ - N+(D+) == 0 :', Dp*div(Np) - apply(Np, Dp) == 0)
    print('terms of N+(K):', len(apply(Np, Kskew)))
