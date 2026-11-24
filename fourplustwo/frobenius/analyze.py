"""Read the output line of ToricControlledReduction and analyse the characteristic polynomial of Frobenius on
H^3_prim(T): symmetry check, trace check against pointcount.py, factorisation over Q, root-of-unity ratio test."""
import sys, json
from flint import fmpz_poly, fmpz
line = open(sys.argv[1]).read().strip()
fields = line.split(':')
p = int(fields[5]); hodge = json.loads(fields[6]); zeta = [int(z) for z in json.loads(fields[7])]
print('p =', p, ' Hodge numbers', hodge, ' degree', len(zeta) - 1)
P = fmpz_poly(zeta)                       # coefficient list, low degree first (as printed by the library)
n = P.degree()
# functional equation: weight 3, so roots pair as alpha <-> p^3/alpha
ok_fe = all(abs(zeta[i]) * p**(3*max(0, n//2 - i)) == abs(zeta[n-i]) * p**(3*max(0, i - n//2)) for i in range(n+1))
print('functional equation (weight 3) holds up to sign:', ok_fe)
print('leading/constant coefficients:', zeta[-1], '...', 'log_p|const| =', len(str(abs(zeta[0]))) )
print('next-to-leading coefficient (= -trace or trace of Frobenius, by convention):', zeta[-2], ' / low end:', zeta[1])
c, fac = P.factor()
print('content', c, ' factor degrees with multiplicity:', sorted((f.degree(), m) for f, m in fac))
for f, m in sorted(fac, key=lambda t: t[0].degree()):
    co = [int(x) for x in f.coeffs()]
    print(f'  degree {f.degree()} (x{m}): trace-type coefficients {co[-2] if len(co) > 1 else None} (high) {co[1] if len(co) > 1 else None} (low); lead {co[-1]}')
json.dump({'p': p, 'hodge': hodge, 'zeta': [str(z) for z in zeta],
           'factors': [([str(x) for x in f.coeffs()], m) for f, m in fac]}, open(f'frobenius_p{p}.json', 'w'))
