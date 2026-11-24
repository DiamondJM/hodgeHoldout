"""Validation of the coset patch against the unpatched program on two curves.
  g2 : y^2 = x^6 + 3x^4 + 5x^2 + 7 over F_13, involution x -> -x        (pieces: x-exponent even / odd)
  pic: y^3 = x^4 + 2x^3 + 5x + 3 over F_13, automorphism y -> zeta_3 y  (pieces: y-exponent 1, 2 mod 3;
       Hodge numbers (2,1) and (1,2), not symmetric)
The product of the characteristic polynomials of the pieces must equal the zeta polynomial computed by the
stock readfile.exe.   usage: python3 validate.py <dir of the patched ToricControlledReduction build>"""
import sys, os, subprocess, tempfile
from flint import fmpz_mat, fmpz_poly
B = os.path.join(sys.argv[1], 'build', 'examples'); here = os.path.dirname(os.path.abspath(__file__))
def piece(inp, cons, N, tmp):
    out = os.path.join(tmp, 'o.txt')
    subprocess.run([os.path.join(B, 'coset_frob.exe'), inp, out, cons, N], check=True, stdout=subprocess.DEVNULL)
    d = {}; rows = {}
    for line in open(out):
        if line.startswith('row'):
            h, v = line.split(':'); rows[int(h.split()[1])] = [int(x) for x in v.split()]
        else:
            k, _, v = line.strip().partition(' '); d[k] = v.strip()
    xin = [int(x) for x in d['X_in_Y'].split()]; n = len(xin)
    if n == 0: return fmpz_poly([1])
    return fmpz_mat(n, n, [rows[j][xin[i]] for i in range(n) for j in range(n)]).charpoly()
ok = True
with tempfile.TemporaryDirectory() as tmp:
    for name, cons, N, mod in (('g2', ['1 0 2 0', '1 0 2 1'], '4,3', 13**3), ('pic', ['0 1 3 0', '0 1 3 1', '0 1 3 2'], '5,4', 13**4)):
        inp = os.path.join(here, f'in_{name}.txt'); ref = os.path.join(tmp, 'ref.txt')
        subprocess.run([os.path.join(B, 'readfile.exe'), inp, ref], check=True, stdout=subprocess.DEVNULL)
        zeta = [int(x) for x in open(ref).read().strip().split(':')[-1].strip('[]').split(',')]
        prod = fmpz_poly([1])
        for c in cons: prod *= piece(inp, c, N, tmp)
        got = [int(c) % mod for c in prod.coeffs()]
        same = got == [z % mod for z in zeta]
        ok &= same
        print(name, 'stock zeta', zeta, '| product of pieces mod', mod, 'agrees:', same)
print('ALL OK' if ok else 'FAILED')
