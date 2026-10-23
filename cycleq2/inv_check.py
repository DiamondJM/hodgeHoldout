import random
def s4(a,b,c,d,e,f,m): return (216*a*b*c*m + 48*(a*e*e*f + b*d*f*f + c*d*d*e) - 24*d*e*f*m - m**4)  # = 48 s4
def s6(a,b,c,d,e,f,m): return (5832*a*a*b*b*c*c + 864*a*a*c*e**3 + 864*a*b*b*f**3 + 1296*a*b*c*d*e*f - 540*a*b*c*m**3
    - 864*a*b*e*f*f*m - 864*a*c*d*e*e*m + 72*a*e*e*f*m*m + 864*b*c*c*d**3 - 864*b*c*d*d*f*m + 72*b*d*f*f*m*m
    + 72*c*d*d*e*m*m - 216*d*d*e*e*f*f - 36*d*e*f*m**3 - m**6)                                         # = 216 s6
def count_cubic(co, p):
    a,b,c,d,e,f,m = co
    G = lambda X,Y,Z: (a*X**3+b*Y**3+c*Z**3+d*X*X*Y+e*Y*Y*Z+f*Z*Z*X+m*X*Y*Z) % p
    return (sum(1 for X in range(p) for Y in range(p) if G(X,Y,1)==0) + sum(1 for X in range(p) if G(X,1,0)==0)
            + (1 if G(1,0,0)==0 else 0))
def count_w(A, B, p):  # eta^2 = xi^3 + A xi + B
    sq = {}
    for t in range(p): sq[t*t%p] = sq.get(t*t%p,0)+1
    return 1 + sum(sq.get((x**3+A*x+B)%p,0) for x in range(p))
if __name__ == '__main__':
    random.seed(7); bad = 0
    for p in (101,103,107,109):
        for _ in range(5):
            co = [random.randrange(p) for _ in range(7)]
            A = s4(*co)*pow(48,p-2,p) % p; B = (-s6(*co)*pow(216*4,p-2,p)) % p
            nc, nw = count_cubic(co,p), count_w(A,B,p)
            if (4*A**3+27*B*B) % p == 0: continue
            bad += nc != nw
            print(p, co, nc, nw, 'OK' if nc==nw else 'MISMATCH')
    print('mismatches:', bad)
