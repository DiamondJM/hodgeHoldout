"""Fixed-denominator certificate test for any catalogue instance (modular evidence, not proof).

For a fixed homogeneous D, the cleared condition of formal/README.md
    A D^2 - q D sum_i N_i dF/dx_i + F (D sum_i dN_i/dx_i - sum_i N_i dD/dx_i) = F^(q+1) Q
is linear in (N, Q).  We test solvability mod a prime with the full numerator space
(restricted only by the global Y-parity forced by F, A and a Y-even D).
Usage: python3 fixed_d.py <data-dir> <instance-id> [max_candidates]
"""
import sys, os, re, itertools, time, json
from flint import fmpq_mpoly_ctx, fmpq, nmod_mat

P = 268435399
ctx = fmpq_mpoly_ctx.get(('X0', 'X1', 'X2', 'Y0', 'Y1', 'Y2'))
V = ctx.gens()
NAMES = {'X0': V[0], 'X1': V[1], 'X2': V[2], 'Y0': V[3], 'Y1': V[4], 'Y2': V[5]}


def parse_rec(path):
    txt = open(path).read()
    out = {}
    for key in ('q', 'F', 'A'):
        m = re.search(r'^%s:(.*?)(?=^\S)' % key, txt, re.S | re.M)
        out[key] = ' '.join(m.group(1).split())
    q = int(out['q'])
    ev = lambda s: eval(s.replace('/', '*fmpq(1)/'), {'fmpq': fmpq}, dict(NAMES))
    return ev(out['F']), q, ev(out['A'])


def monoms(n):
    if n < 0:
        return []
    res = []
    for c in itertools.combinations(range(n + 5), 5):
        e, prev = [], -1
        for ci in c:
            e.append(ci - prev - 1); prev = ci
        e.append(n + 4 - prev)
        res.append(tuple(e))
    return res


def mono(e):
    r = ctx.from_dict({e: 1})
    return r


def ypar(e):
    return (e[3] + e[4] + e[5]) % 2


def modp(c):
    c = fmpq(c)
    return int(c.p) * pow(int(c.q), -1, P) % P


def test(F, q, A, D):
    d = D.total_degree()
    dn = d + 6 * q - 5
    J = [F.derivative(i) for i in range(6)]
    dD = [D.derivative(i) for i in range(6)]
    dpar = ypar(next(iter(D.to_dict())))
    cols, labels = [], []
    for i in range(6):
        want = (1 + dpar + (1 if i >= 3 else 0)) % 2  # parity making each term Y-odd
        for e in monoms(dn):
            if ypar(e) != want:
                continue
            m = mono(e)
            cols.append(-q * D * m * J[i] + F * (D * m.derivative(i) - m * dD[i]))
    Fq = F ** (q + 1)
    for e in monoms(A.total_degree() + 2 * d - 6 * (q + 1)):
        if ypar(e) != 1:
            continue
        cols.append(-Fq * mono(e))
    rhs = A * D * D
    rows = {}
    for p in cols + [rhs]:
        for m in p.monoms():
            if m not in rows:
                rows[m] = len(rows)
    M = nmod_mat(len(rows), len(cols) + 1, P)
    for j, p in enumerate(cols + [rhs]):
        for m, c in zip(p.monoms(), p.coeffs()):
            M[rows[m], j] = modp(c)
    full = M.rank()
    M0 = nmod_mat(len(rows), len(cols), P)
    for j, p in enumerate(cols):
        for m, c in zip(p.monoms(), p.coeffs()):
            M0[rows[m], j] = modp(c)
    r0 = M0.rank()
    return r0 == full, len(rows), len(cols), r0


def candidates(F):
    out = []
    for k in (2, 3, 4):
        for S in itertools.combinations(range(6), k):
            out.append(('pow' + ''.join(map(str, S)), sum(V[i] ** 6 for i in S)))
    fd = F.to_dict()
    for k in (2, 3, 4, 5):
        for S in itertools.combinations(range(6), k):
            sub = {e: c for e, c in fd.items() if all(e[i] == 0 for i in range(6) if i not in S)}
            if len(sub) > k:  # has a coupling, not just pure powers
                out.append(('Fsub' + ''.join(map(str, S)), ctx.from_dict(sub)))
    seen, res = set(), []
    for lab, D in out:
        key = str(D)
        if key in seen:
            continue
        seen.add(key); res.append((lab, D))
    return res


if __name__ == '__main__':
    root, inst = sys.argv[1], sys.argv[2]
    F, q, A = parse_rec(os.path.join(root, inst, 'instance.rec'))
    assert F.total_degree() == 6
    # control: A itself must not be trivially exact with D = 1 (degree check of the system)
    cands = candidates(F)
    if len(sys.argv) > 3:
        cands = cands[:int(sys.argv[3])]
    done = set()
    logp = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'logs', inst + '.log')
    if os.path.exists(logp):
        done = {l.split()[1] for l in open(logp) if l.startswith(inst + ' ')}
    if not done:
        print(f'# {inst} q={q} candidates={len(cands)}', flush=True)
    for lab, D in cands:
        if lab in done:
            continue
        t = time.time()
        ok, nr, nc, r0 = test(F, q, A, D)
        print(f'{inst} {lab:14} {"SOLVABLE" if ok else "no"} rows={nr} cols={nc} rank={r0} {time.time()-t:.0f}s', flush=True)
