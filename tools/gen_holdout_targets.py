#!/usr/bin/env python3
"""Derive proposal folders for the remaining q=1 holdout targets from fqlx's accepted
holdout proof (hodge-computer/sextics PR #128).

The accepted construction is target-independent except for (i) the quotient source on the
weighted hypersurface H, (ii) the deck-trace companion, and (iii) the trivial source
bookkeeping lemmas.  For a Y-odd monomial target A = X^a Y0^b0 Y1^b1 Y2^b2 on the Fermat
cover (Y0, Y1, Y2) = (alpha T, y, beta T) the pulled-back density, symmetrised under the
interchange y <-> T, descends to the polynomial source

    B = (A (-T/alpha^5) - iota(A (-T/alpha^5))) / (2 (y^2 - T^2))

on H (coordinates X0, X1, X2, S = y^2+T^2, P = yT), and the reflected companion equals
A (y/T)^k with k = b0 + b2 + 1 - b1.  The companion is killed by the deck trace whenever
k is not divisible by six.  This script writes, for each target, copies of all accepted
Lean modules with the target-specific declarations replaced, and checks every scalar
identity it emits with sympy before writing.

Usage: gen_holdout_targets.py SEXTICS_ROOT OUT_ROOT [instance ...]
"""
import re
import shutil
import sys
from pathlib import Path

import sympy as sp

SRC = Path(sys.argv[1]) / 'data' / 'holdout'
OUT = Path(sys.argv[2])
ONLY = set(sys.argv[3:])

X0, X1, X2, Y0, Y1, Y2 = Z6 = sp.symbols('X0 X1 X2 Y0 Y1 Y2')
a, b, x0, x1, x2, y, t = sp.symbols('a b x0 x1 x2 y t')
S, P = sp.symbols('S P')
COVER = {X0: x0, X1: x1, X2: x2, Y0: a * t, Y1: y, Y2: b * t}

TARGETS = {
    # instance id: (exponents of A in X0,X1,X2,Y0,Y1,Y2)
    'holdout': (3, 0, 0, 3, 0, 0),
    'holdout-x13-y13': (0, 3, 0, 0, 3, 0),
    'holdout-p3': (0, 0, 3, 0, 0, 3),
    'holdout-x12-p-y02': (0, 2, 1, 2, 0, 1),
    'holdout-p-y14': (0, 0, 1, 0, 4, 1),
    'holdout-x1-y04-y1': (0, 1, 0, 4, 1, 0),
    'holdout-x0-y03-y12': (1, 0, 0, 3, 2, 0),
    'holdout-all-six': (1, 1, 1, 1, 1, 1),
    'holdout-x0-x14-y0': (1, 4, 0, 1, 0, 0),
    'holdout-x04-p': (4, 0, 1, 0, 0, 1),
}


def lean_mono6(exps, prefix='MvPolynomial.X '):
    """Left-associated product X i^e matching the verifier's translation of instance.rec."""
    parts = []
    for i, e in enumerate(exps):
        if e == 0:
            continue
        parts.append(f'{prefix}{i}' + (f'^{e}' if e > 1 else ''))
    return '*'.join(parts) if parts else '1'


def lean_poly6(expr, prefix='MvPolynomial.X '):
    """Lean text of a polynomial in Z6 with integer coefficients (sum of coefficient*monomial)."""
    expr = sp.expand(expr)
    if expr == 0:
        return '0'
    poly = sp.Poly(expr, *Z6)
    terms = []
    for mon, c in poly.terms():
        c = int(c)
        m = lean_mono6(mon, prefix)
        if m == '1':
            terms.append(str(c))
        elif c == 1:
            terms.append(m)
        else:
            terms.append(f'{c}*{m}')
    return '+'.join(terms)


def cover_of_poly6(expr):
    """Lean text in cover coordinates of the image of a Fin 6 polynomial (same product order
    as lean_poly6 so that `simp only [map_mul, map_pow, ...]; rfl` matches)."""
    expr = sp.expand(expr)
    if expr == 0:
        return '0'
    names = ['coverX0', 'coverX1', 'coverX2', '(coverAlpha*coverT)', 'coverY', '(coverBeta*coverT)']
    poly = sp.Poly(expr, *Z6)
    terms = []
    for mon, c in poly.terms():
        c = int(c)
        parts = [f'{names[i]}' + (f'^{e}' if e > 1 else '') for i, e in enumerate(mon) if e]
        m = '*'.join(parts)
        terms.append(m if c == 1 else f'{c}*{m}')
    return '+'.join(terms)


def scalar_of_poly6(expr):
    names = ['x0', 'x1', 'x2', '(a*t)', 'y', '(b*t)']
    expr = sp.expand(expr)
    if expr == 0:
        return '0'
    poly = sp.Poly(expr, *Z6)
    terms = []
    for mon, c in poly.terms():
        c = int(c)
        parts = [f'{names[i]}' + (f'^{e}' if e > 1 else '') for i, e in enumerate(mon) if e]
        m = '*'.join(parts)
        terms.append(m if c == 1 else f'{c}*{m}')
    return '+'.join(terms)


def sympy_of_scalar(text):
    return sp.sympify(text.replace('^', '**'), locals={'a': a, 'b': b, 'x0': x0, 'x1': x1, 'x2': x2, 'y': y, 't': t})


def analyse(exps):
    A = sp.Mul(*[v ** e for v, e in zip(Z6, exps)])
    b0, b1, b2 = exps[3], exps[4], exps[5]
    k = b0 + b2 + 1 - b1
    assert k % 6 != 0 and k % 2 == 0, (exps, k)
    Ac = A.subs(COVER)
    dens = sp.expand(Ac * (-t / a ** 5))
    refl = sp.expand(-dens.subs({y: t, t: y}, simultaneous=True))
    Bq = sp.cancel((dens + refl) / (2 * (y ** 2 - t ** 2)))
    # express the symmetric polynomial Bq*a^5 in S,P by matching
    Bp = sp.Poly(sp.expand(Bq * a ** 5), y, t)
    deg = Bp.total_degree()
    cs, expr = [], 0
    for i in range(deg // 2 + 1):
        for j in range(deg // 2 + 1 - i):
            c = sp.Symbol(f'c_{i}_{j}')
            cs.append(c)
            expr += c * S ** i * P ** j
    diff = sp.Poly(sp.expand(expr.subs({S: y ** 2 + t ** 2, P: y * t}) - Bq * a ** 5), y, t)
    sol = sp.solve(diff.coeffs(), cs, dict=True)
    assert sol
    BSP = sp.expand(expr.subs(sol[0]).subs({c: 0 for c in cs}) / a ** 5)
    # companion polynomial C (physical) and E
    if k > 0:
        C = A * Y1 ** k
        Ekind = ('inv', k)
    else:
        assert b1 >= -k
        C = sp.cancel(A / Y1 ** (-k))
        Ekind = ('pow', -k)
    # check: (2 a^5 (t^2-y^2)/t) * B = A_c - C_c * E
    E = t ** (-k) if k > 0 else t ** (-k)
    E = (1 / t ** k) if k > 0 else t ** (-k)
    Bc = BSP.subs({S: y ** 2 + t ** 2, P: y * t})
    assert sp.simplify((2 * a ** 5 * (t ** 2 - y ** 2) / t) * Bc - (Ac - C.subs(COVER) * E)) == 0
    # weighted degree 5 check
    for mon in sp.Poly(BSP, x0, x1, x2, S, P).monoms():
        assert sum(e * w for e, w in zip(mon, (1, 1, 1, 2, 2))) == 5, mon
    return A, C, BSP, k, Ekind


def split_coef_mono(BSP):
    """BSP = coef(a,b) * monomial(x0,x1,x2,S,P)."""
    poly = sp.Poly(BSP, x0, x1, x2, S, P)
    terms = poly.terms()
    assert len(terms) == 1, terms
    mon, coef = terms[0]
    return sp.simplify(coef), mon


def lean_coef(coef):
    """Coefficient in FermatCoefficientField ℂ as Lean text, and its cover-field image text as
    simp produces it (map_div₀/map_neg/map_one/map_ofNat/map_pow/map_mul)."""
    num, den = sp.fraction(sp.together(coef))
    # den = 2*a^n, num = ±1 or ±b^m
    dn = sp.Poly(den, a)
    assert dn.LC() == 2 and len(dn.terms()) == 1
    n = dn.degree()
    sign = 1
    if num.could_extract_minus_sign():
        sign = -1
        num = -num
    m = sp.Poly(num, b).degree() if num != 1 else 0
    assert sp.simplify(num - b ** m) == 0, num
    alpha = '(genericBaseAlpha ℂ)'
    beta = '(genericBaseBeta ℂ)'
    den_f = f'(2*{alpha}' + (f'^{n})' if n > 1 else ')')
    den_c = f'(2*coverAlpha' + (f'^{n})' if n > 1 else ')')
    if m == 0:
        num_f, num_c = '1', '1'
    else:
        num_f = f'{beta}' + (f'^{m}' if m > 1 else '')
        num_c = 'coverBeta' + (f'^{m}' if m > 1 else '')
    if sign < 0:
        num_f, num_c = f'(-{num_f})' if m == 0 else f'-{num_f}', f'(-{num_c})' if m == 0 else f'-{num_c}'
    field = f'{num_f}/{den_f}'
    cover = f'{num_c}/{den_c}'
    scalar = field.replace('(genericBaseAlpha ℂ)', 'a').replace('(genericBaseBeta ℂ)', 'b')
    return field, cover, scalar


def mono5(mon, names):
    parts = [f'{names[i]}' + (f'^{e}' if e > 1 else '') for i, e in enumerate(mon) if e]
    return '*'.join(parts) if parts else '1'


def d0_mono5(mon):
    """Partial derivative in X 0 of the Fin-5 monomial: (coefficient, monomial) or None."""
    if mon[0] == 0:
        return None
    e = list(mon)
    c = e[0]
    e[0] -= 1
    return c, tuple(e)


def build(instance, exps):
    A, C, BSP, k, (ekind, epow) = analyse(exps)
    dA = sp.diff(A, X0)
    dC = sp.diff(C, X0)
    coef, qmon = split_coef_mono(BSP)
    coef_f, coef_c, coef_s = lean_coef(coef)
    names5 = ['X 0', 'X 1', 'X 2', 'X 3', 'X 4']
    cover5 = ['coverX0', 'coverX1', 'coverX2', '(coverY^2+coverT^2)', '(coverY*coverT)']
    scalar5 = ['x0', 'x1', 'x2', '(y^2+t^2)', '(y*t)']
    qmono_lean = mono5(qmon, names5)
    qmono_cover = mono5(qmon, cover5)
    qmono_scalar = mono5(qmon, scalar5)
    dq = d0_mono5(qmon)
    # E text
    if ekind == 'inv':
        E_cover = f'(coverT^{epow})⁻¹'
        E_scalar_div = f'/t^{epow}'  # C_scalar/t^epow
        trace_lemma = {4: 'commonCover_trace_inverse_fourth', 2: 'commonCover_trace_inverse_square'}[epow]
    else:
        E_cover = f'coverT^{epow}'
        E_scalar_div = f'*t^{epow}'
        trace_lemma = {2: 'commonCover_trace_square'}[epow]
    A6, C6 = lean_poly6(A), lean_poly6(C)
    dA6, dC6 = lean_poly6(dA), lean_poly6(dC)
    A_cov, C_cov, dA_cov, dC_cov = cover_of_poly6(A), cover_of_poly6(C), cover_of_poly6(dA), cover_of_poly6(dC)
    A_sc, C_sc, dA_sc, dC_sc = scalar_of_poly6(A), scalar_of_poly6(C), scalar_of_poly6(dA), scalar_of_poly6(dC)
    B_sc = f'{qmono_scalar}*{coef_s}'
    B_cov = f'{qmono_cover}*{coef_c}'
    if dq is None:
        dB_sc, dB_cov = '0', '0'
    else:
        c0, dmon = dq
        pre = f'{c0}*' if c0 > 1 else ''
        dB_sc = f'{pre}{mono5(dmon, scalar5)}*{coef_s}'
        dB_cov = f'{pre}{mono5(dmon, cover5)}*{coef_c}'
    # sympy re-check of the two scalar identities exactly as emitted
    sB, sA, sC, sdB, sdA, sdC = map(sympy_of_scalar, (B_sc, A_sc, C_sc, dB_sc, dA_sc, dC_sc))
    sE = sympy_of_scalar('1' + E_scalar_div)
    lhs = (2 * a ** 5 * (t ** 2 - y ** 2) / t) * sB
    assert sp.simplify(lhs - (sA - sC * sE)) == 0, instance
    g, h = sp.symbols('g h')
    lhs2 = (2 * a ** 5 * (t ** 2 - y ** 2) / t) * ((sdB * g - sB * h) / g ** 2)
    rhs2 = ((sdA * g - sA * h) / g ** 2) - ((sdC * g - sC * h) / g ** 2) * sE
    assert sp.simplify(lhs2 - rhs2) == 0, instance
    # which scalar variables occur
    used = [v for v in ('a', 'b', 'x0', 'x1', 'x2', 'y', 't')
            if re.search(rf'\b{v}\b', ' '.join((B_sc, A_sc, C_sc, dB_sc, dA_sc, dC_sc)))]
    if 'a' not in used:
        used.insert(0, 'a')
    if 't' not in used:
        used.append('t')
    if 'y' not in used:
        used.insert(used.index('t'), 'y')
    covername = {'a': 'coverAlpha', 'b': 'coverBeta', 'x0': 'coverX0', 'x1': 'coverX1', 'x2': 'coverX2',
                 'y': 'coverY', 't': 'coverT'}
    scalar_args = ' '.join(used)
    cover_args = ' '.join(covername[v] for v in used)

    # homogeneity proof: exponent-1 factors need pow_one to match the bare `X i` in the def
    hom_haves = ''
    hom_parts = []
    for i, e in enumerate(exps):
        if e == 0:
            continue
        if e == 1:
            hom_haves += (f'  have hX{i} : (MvPolynomial.X (R := ℂ) ({i} : Fin 6)).IsHomogeneous 1 := by\n'
                          f'    simpa only [pow_one] using isHomogeneous_X_pow (R := ℂ) ({i} : Fin 6) 1\n')
            hom_parts.append(f'hX{i}')
        else:
            hom_parts.append(f'(isHomogeneous_X_pow (R := ℂ) ({i} : Fin 6) {e})')
    hom = hom_parts[0]
    for p in hom_parts[1:]:
        hom = f'({hom}.mul {p})'

    files = {p.name: p.read_text() for p in SRC.glob('*.lean')}

    def sub(name, old, new, count=1):
        text = files[name]
        assert text.count(old) == count, (instance, name, old[:60], text.count(old))
        files[name] = text.replace(old, new)

    credit = ('/- Adapted for the instance `' + instance + '` from the accepted holdout proof by `fqlx` '
              '(hodge-computer/sextics PR #128, prepared with OpenAI ChatGPT assistance); the target-specific '
              'source, companion and trace data are replaced, all other modules are unchanged. Adaptation '
              'prepared with Claude Code assistance for `DiamondJM`. -/\n')

    # ---- HomogeneousCertificate.lean
    sub('HomogeneousCertificate.lean',
        '/-- The protected holdout numerator in the original coordinate order. -/\n'
        'def holdoutSource : HodgeComputer.Poly := MvPolynomial.X 0^3*MvPolynomial.X 3^3\n',
        f'/-- The protected numerator of `{instance}` in the original coordinate order. -/\n'
        f'def holdoutSource : HodgeComputer.Poly := {A6}\n\n'
        '/-- The physical polynomial multiplying the deck-trace correction term. -/\n'
        f'def holdoutCompanion : HodgeComputer.Poly := {C6}\n')
    sub('HomogeneousCertificate.lean',
        'theorem holdoutSource_isHomogeneous : holdoutSource.IsHomogeneous 6 :=\n'
        '  (isHomogeneous_X_pow (0 : Fin 6) 3).mul (isHomogeneous_X_pow (3 : Fin 6) 3)\n',
        'theorem holdoutSource_isHomogeneous : holdoutSource.IsHomogeneous 6 := by\n'
        + hom_haves + f'  exact {hom}\n')
    files['HomogeneousCertificate.lean'] = credit + files['HomogeneousCertificate.lean']

    # ---- CoverScalars.lean
    sub('CoverScalars.lean',
        'theorem cover_source_identity (a x y t : K) (ha : a ≠ 0) (ht : t ≠ 0) :\n'
        '    (2*a^5*(t^2-y^2)/t) * (x^3*(y^2+t^2)/(2*a^2)) =\n'
        '      x^3*(a*t)^3*(1-y^4/t^4) := by\n'
        '  field_simp\n'
        '  ring\n',
        f'theorem cover_source_identity ({scalar_args} : K) (ha : a ≠ 0) (ht : t ≠ 0) :\n'
        f'    (2*a^5*(t^2-y^2)/t) * ({B_sc}) =\n'
        f'      {A_sc} - {C_sc}{E_scalar_div} := by\n'
        '  field_simp\n'
        '  ring\n')
    sub('CoverScalars.lean',
        'theorem cover_normal_source_identity (a x y t g h : K)\n'
        '    (ha : a ≠ 0) (ht : t ≠ 0) :\n'
        '    (2*a^5*(t^2-y^2)/t) *\n'
        '      (((3*x^2*(y^2+t^2)/(2*a^2))*g -\n'
        '        (x^3*(y^2+t^2)/(2*a^2))*h)/g^2) =\n'
        '      ((3*x^2*(a*t)^3*g-x^3*(a*t)^3*h)/g^2)*(1-y^4/t^4) := by\n',
        f'theorem cover_normal_source_identity ({scalar_args} g h : K)\n'
        '    (ha : a ≠ 0) (ht : t ≠ 0) :\n'
        '    (2*a^5*(t^2-y^2)/t) *\n'
        f'      ((({dB_sc})*g -\n'
        f'        ({B_sc})*h)/g^2) =\n'
        f'      ((({dA_sc})*g-({A_sc})*h)/g^2) -\n'
        f'        ((({dC_sc})*g-({C_sc})*h)/g^2){E_scalar_div} := by\n')
    files['CoverScalars.lean'] = credit + files['CoverScalars.lean']

    # ---- DeckTrace.lean: append generalised lemmas before `end HoldoutConstruction`
    sub('DeckTrace.lean',
        'end HoldoutConstruction\n',
        '''/-- A deck homomorphism scaling T by a scalar whose n-th power is nontrivial
kills T^(-n) under normalized trace. -/
theorem normalizedTrace_inv_pow_zero
    (σ : L →ₐ[K] L) (zeta : K) (n : ℕ) (hzeta : zeta^n ≠ 1)
    (T : L) (scale : σ T = algebraMap K L zeta * T) :
    Algebra.normalizedTrace K L ((T^n)⁻¹) = 0 := by
  apply normalizedTrace_eigen_zero σ ((zeta^n)⁻¹)
  · intro h
    apply hzeta
    have hi := congrArg (fun x : K => x⁻¹) h
    simpa only [inv_inv, inv_one] using hi
  · simp only [map_inv₀, map_pow, scale, mul_pow, mul_inv_rev]
    ring

/-- The same deck homomorphism kills the positive power T^n. -/
theorem normalizedTrace_pow_zero
    (σ : L →ₐ[K] L) (zeta : K) (n : ℕ) (hzeta : zeta^n ≠ 1)
    (T : L) (scale : σ T = algebraMap K L zeta * T) :
    Algebra.normalizedTrace K L (T^n) = 0 := by
  apply normalizedTrace_eigen_zero σ (zeta^n) hzeta
  simp only [map_pow, scale, mul_pow]

/-- A source of the form r - c*E with trace-free E has normalized trace r. -/
theorem normalizedTrace_deck_difference
    (E : L) (hE : Algebra.normalizedTrace K L E = 0) (r c : K) :
    Algebra.normalizedTrace K L (algebraMap K L r - algebraMap K L c * E) = r := by
  have hlin : Algebra.normalizedTrace K L (algebraMap K L c * E) = 0 := by
    have heq : algebraMap K L c * E = c • E := by
      simp only [Algebra.smul_def]
    rw [heq, map_smul, hE, smul_zero]
  rw [map_sub, Algebra.normalizedTrace_algebraMap_apply_eq_self, hlin, sub_zero]

end HoldoutConstruction
''')
    files['DeckTrace.lean'] = credit + files['DeckTrace.lean']

    # ---- CoverDeckField.lean
    sub('CoverDeckField.lean',
        'theorem exists_nontrivial_sixth_root :\n'
        '    ∃ z : ℂ, z^6=1 ∧ z ≠ 0 ∧ z^4 ≠ 1 := by\n',
        'theorem exists_nontrivial_sixth_root :\n'
        '    ∃ z : ℂ, z^6=1 ∧ z ≠ 0 ∧ z^4 ≠ 1 ∧ z^2 ≠ 1 := by\n')
    sub('CoverDeckField.lean',
        '  refine ⟨z, ?_, h0, ?_⟩\n'
        '  · rw [show 6=3*2 by decide, pow_mul, h3, one_pow]\n'
        '  · intro h4\n'
        '    apply h1\n'
        '    calc\n'
        '      z = z^3*z := by rw [h3, one_mul]\n'
        '      _ = z^4 := by ring\n'
        '      _ = 1 := h4\n',
        '  refine ⟨z, ?_, h0, ?_, ?_⟩\n'
        '  · rw [show 6=3*2 by decide, pow_mul, h3, one_pow]\n'
        '  · intro h4\n'
        '    apply h1\n'
        '    calc\n'
        '      z = z^3*z := by rw [h3, one_mul]\n'
        '      _ = z^4 := by ring\n'
        '      _ = 1 := h4\n'
        '  · intro h2\n'
        '    have hz2 : z = -2 := by linear_combination hq - h2\n'
        '    rw [hz2] at h3\n'
        '    norm_num at h3\n')
    sub('CoverDeckField.lean',
        '  obtain ⟨z,hz,hz0,hz4⟩ := exists_nontrivial_sixth_root\n'
        '  apply normalizedTrace_inv_fourth_zero (physicalDeckAlgHom z hz hz0)\n',
        '  obtain ⟨z,hz,hz0,hz4,_⟩ := exists_nontrivial_sixth_root\n'
        '  apply normalizedTrace_inv_fourth_zero (physicalDeckAlgHom z hz hz0)\n')
    sub('CoverDeckField.lean',
        'end HoldoutConstruction\n',
        '''theorem commonCover_trace_inverse_square :
    Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      ((coverT^2)⁻¹) = 0 := by
  obtain ⟨z,hz,hz0,_,hz2⟩ := exists_nontrivial_sixth_root
  apply normalizedTrace_inv_pow_zero (physicalDeckAlgHom z hz hz0)
    (algebraMap ℂ HoldoutFunctionField z) 2 ?_ coverT (physicalDeckAlgHom_T z hz hz0)
  intro h
  apply hz2
  apply (algebraMap ℂ HoldoutFunctionField).injective
  simpa only [map_pow, map_one] using h

theorem commonCover_trace_square :
    Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      (coverT^2) = 0 := by
  obtain ⟨z,hz,hz0,_,hz2⟩ := exists_nontrivial_sixth_root
  apply normalizedTrace_pow_zero (physicalDeckAlgHom z hz hz0)
    (algebraMap ℂ HoldoutFunctionField z) 2 ?_ coverT (physicalDeckAlgHom_T z hz hz0)
  intro h
  apply hz2
  apply (algebraMap ℂ HoldoutFunctionField).injective
  simpa only [map_pow, map_one] using h

end HoldoutConstruction
''')
    files['CoverDeckField.lean'] = credit + files['CoverDeckField.lean']

    # ---- HoldoutCertificateClosure.lean
    sub('HoldoutCertificateClosure.lean',
        '''private theorem physical_normal_source_trace
    (T : CommonCoverFunctionField)
    (hT : Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      ((T^4)⁻¹) = 0) (r c : HoldoutFunctionField) :
    Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      (algebraMap HoldoutFunctionField CommonCoverFunctionField r *
        (1 - algebraMap HoldoutFunctionField CommonCoverFunctionField c * (T^4)⁻¹)) = r := by
  have hlin : Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      (algebraMap HoldoutFunctionField CommonCoverFunctionField r *
        algebraMap HoldoutFunctionField CommonCoverFunctionField c * (T^4)⁻¹) = 0 := by
    have heq : algebraMap HoldoutFunctionField CommonCoverFunctionField r *
        algebraMap HoldoutFunctionField CommonCoverFunctionField c * (T^4)⁻¹ =
          (r*c) • (T^4)⁻¹ := by
      simp only [Algebra.smul_def, map_mul]
    rw [heq, map_smul, hT, smul_zero]
  rw [mul_sub, mul_one, ← mul_assoc, map_sub,
    Algebra.normalizedTrace_algebraMap_apply_eq_self, hlin, sub_zero]
''',
        '''/-- The physical normal-divergence source of the companion polynomial. -/
def physicalCompanionNormalSource : HoldoutFunctionField :=
  (physicalResidueMap (integerPartial 0 holdoutCompanion) * physicalNormal -
    physicalResidueMap holdoutCompanion *
      physicalResidueMap (integerPartial 0 (integerPartial 0 holdoutSextic))) /
        physicalNormal^2

private theorem physical_normal_source_trace
    (E : CommonCoverFunctionField)
    (hE : Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField E = 0)
    (r c : HoldoutFunctionField) :
    Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      (algebraMap HoldoutFunctionField CommonCoverFunctionField r -
        algebraMap HoldoutFunctionField CommonCoverFunctionField c * E) = r := by
  have hlin : Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      (algebraMap HoldoutFunctionField CommonCoverFunctionField c * E) = 0 := by
    have heq : algebraMap HoldoutFunctionField CommonCoverFunctionField c * E = c • E := by
      simp only [Algebra.smul_def]
    rw [heq, map_smul, hE, smul_zero]
  rw [map_sub, Algebra.normalizedTrace_algebraMap_apply_eq_self, hlin, sub_zero]
''')
    sub('HoldoutCertificateClosure.lean',
        '''theorem holdout_hasCertificate_of_cover_residue
    (T : CommonCoverFunctionField)
    (hT : Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField
      ((T^4)⁻¹) = 0)
    (w : Fin 5 → CommonCoverFunctionField)
    (equation :
      algebraMap HoldoutFunctionField CommonCoverFunctionField physicalNormalSource *
        (1 - algebraMap HoldoutFunctionField CommonCoverFunctionField
          (physicalResidueMap (MvPolynomial.X 4)^4) * (T^4)⁻¹) +
''',
        '''theorem holdout_hasCertificate_of_cover_residue
    (E : CommonCoverFunctionField)
    (hE : Algebra.normalizedTrace HoldoutFunctionField CommonCoverFunctionField E = 0)
    (w : Fin 5 → CommonCoverFunctionField)
    (equation :
      algebraMap HoldoutFunctionField CommonCoverFunctionField physicalNormalSource -
        algebraMap HoldoutFunctionField CommonCoverFunctionField
          physicalCompanionNormalSource * E +
''')
    sub('HoldoutCertificateClosure.lean',
        '''  have heq :
      algebraMap HoldoutFunctionField CommonCoverFunctionField physicalNormalSource *
        (1 - algebraMap HoldoutFunctionField CommonCoverFunctionField
          (physicalResidueMap (MvPolynomial.X 4)^4) * (T^4)⁻¹) +
''',
        '''  have heq :
      algebraMap HoldoutFunctionField CommonCoverFunctionField physicalNormalSource -
        algebraMap HoldoutFunctionField CommonCoverFunctionField
          physicalCompanionNormalSource * E +
''')
    sub('HoldoutCertificateClosure.lean',
        '''      (algebraMap HoldoutFunctionField CommonCoverFunctionField physicalNormalSource *
        (1 - algebraMap HoldoutFunctionField CommonCoverFunctionField
          (physicalResidueMap (MvPolynomial.X 4)^4) * (T^4)⁻¹)) w
''',
        '''      (algebraMap HoldoutFunctionField CommonCoverFunctionField physicalNormalSource -
        algebraMap HoldoutFunctionField CommonCoverFunctionField
          physicalCompanionNormalSource * E) w
''')
    sub('HoldoutCertificateClosure.lean',
        '''      (physical_normal_source_trace T hT physicalNormalSource
        (physicalResidueMap (MvPolynomial.X 4)^4)) heq
''',
        '''      (physical_normal_source_trace E hE physicalNormalSource
        physicalCompanionNormalSource) heq
''')
    files['HoldoutCertificateClosure.lean'] = credit + files['HoldoutCertificateClosure.lean']

    # ---- CoverCertificate.lean
    sub('CoverCertificate.lean',
        '''  have hs : actualCoverJacobian.det*quotientCoverFieldMap coverQuotientNormalSource =
      physicalCoverFieldMap physicalNormalSource *
        (1-physicalCoverFieldMap (physicalResidueMap (MvPolynomial.X 4)^4)*(coverT^4)⁻¹) := by
    rw [actualCoverJacobian_det]
    simpa only [coverQuotientNormalSource, coverQuotientNormal,
      physicalNormalSource, physicalNormal, physicalCoverFieldMap.map_pow] using
        cover_normal_source_binding
''',
        f'''  have hs : actualCoverJacobian.det*quotientCoverFieldMap coverQuotientNormalSource =
      physicalCoverFieldMap physicalNormalSource -
        physicalCoverFieldMap physicalCompanionNormalSource * {E_cover} := by
    rw [actualCoverJacobian_det]
    simpa only [coverQuotientNormalSource, coverQuotientNormal,
      physicalNormalSource, physicalCompanionNormalSource, physicalNormal] using
        cover_normal_source_binding
''')
    sub('CoverCertificate.lean',
        '''  apply holdout_hasCertificate_of_cover_residue coverT commonCover_trace_inverse_fourth v
  change physicalCoverFieldMap physicalNormalSource *
      (1-physicalCoverFieldMap (physicalResidueMap (MvPolynomial.X 4)^4)*(coverT^4)⁻¹) +
''',
        f'''  apply holdout_hasCertificate_of_cover_residue {E_cover} {trace_lemma} v
  change physicalCoverFieldMap physicalNormalSource -
      physicalCoverFieldMap physicalCompanionNormalSource * {E_cover} +
''')
    files['CoverCertificate.lean'] = credit + files['CoverCertificate.lean']

    # ---- CoverSourceBinding.lean
    sub('CoverSourceBinding.lean',
        'def scaledCoverQuotientSource (c : R) : MvPolynomial (Fin 5) R :=\n'
        '  C c*X 0^3*X 3\n\n'
        'theorem scaledCoverQuotientSource_partial (c : R) :\n'
        '    integerPartial 0 (scaledCoverQuotientSource c) = 3*C c*X 0^2*X 3 := by\n'
        '  norm_num [integerPartial_apply, scaledCoverQuotientSource,\n'
        '    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff]\n'
        '  ring\n',
        'def scaledCoverQuotientSource (c : R) : MvPolynomial (Fin 5) R :=\n'
        f'  C c*{qmono_lean}\n\n'
        'theorem scaledCoverQuotientSource_partial (c : R) :\n'
        f'    integerPartial 0 (scaledCoverQuotientSource c) = '
        + ('0' if dq is None else (f'{dq[0]}*' if dq[0] > 1 else '') + f'C c*{mono5(dq[1], names5)}') + ' := by\n'
        '  norm_num [integerPartial_apply, scaledCoverQuotientSource,\n'
        '    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff] <;> ring\n')
    sub('CoverSourceBinding.lean',
        'theorem cover_holdoutSource_partial :\n'
        '    integerPartial 0 holdoutSource = 3*X 0^2*X 3^3 := by\n'
        '  norm_num [integerPartial_apply, holdoutSource, MvPolynomial.pderiv_pow,\n'
        '    MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff]\n'
        '  ring\n',
        'theorem cover_holdoutSource_partial :\n'
        f'    integerPartial 0 holdoutSource = {lean_poly6(dA, "X ")} := by\n'
        '  norm_num [integerPartial_apply, holdoutSource, MvPolynomial.pderiv_pow,\n'
        '    MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff] <;> ring\n\n'
        'theorem cover_holdoutCompanion_partial :\n'
        f'    integerPartial 0 holdoutCompanion = {lean_poly6(dC, "X ")} := by\n'
        '  norm_num [integerPartial_apply, holdoutCompanion, MvPolynomial.pderiv_pow,\n'
        '    MvPolynomial.pderiv_mul, Pi.single_apply, Fin.ext_iff] <;> ring\n')
    sub('CoverSourceBinding.lean',
        'def coverQuotientSource : MvPolynomial (Fin 5) (FermatCoefficientField ℂ) :=\n'
        '  scaledCoverQuotientSource (1/(2*(genericBaseAlpha ℂ)^2))\n',
        'def coverQuotientSource : MvPolynomial (Fin 5) (FermatCoefficientField ℂ) :=\n'
        f'  scaledCoverQuotientSource ({coef_f})\n')
    # physical source values
    sub('CoverSourceBinding.lean',
        'theorem cover_physical_source_value :\n'
        '    physicalCoverFieldMap (ρp holdoutSource) = coverX0^3*(coverAlpha*coverT)^3 := by\n'
        '  simp only [holdoutSource, map_mul, map_pow, physicalCoverFieldMap_residue_X]\n'
        '  rfl\n',
        'theorem cover_physical_source_value :\n'
        f'    physicalCoverFieldMap (ρp holdoutSource) = {A_cov} := by\n'
        '  simp only [holdoutSource, map_mul, map_pow, physicalCoverFieldMap_residue_X]\n'
        '  rfl\n\n'
        'theorem cover_physical_companion_value :\n'
        f'    physicalCoverFieldMap (ρp holdoutCompanion) = {C_cov} := by\n'
        '  simp only [holdoutCompanion, map_mul, map_pow, physicalCoverFieldMap_residue_X]\n'
        '  rfl\n')

    def partial_value_proof(lemma, dexpr):
        if dexpr == 0:
            return f'  rw [{lemma}, map_zero, map_zero]\n'
        return (f'  rw [{lemma}]\n'
                '  simp only [map_mul, map_pow, map_ofNat, physicalCoverFieldMap_residue_X]\n'
                '  rfl\n')

    sub('CoverSourceBinding.lean',
        'theorem cover_physical_source_partial_value :\n'
        '    physicalCoverFieldMap (ρp (integerPartial 0 holdoutSource)) =\n'
        '      3*coverX0^2*(coverAlpha*coverT)^3 := by\n'
        '  rw [cover_holdoutSource_partial]\n'
        '  simp only [map_mul, map_pow, map_ofNat, physicalCoverFieldMap_residue_X]\n'
        '  rfl\n',
        'theorem cover_physical_source_partial_value :\n'
        '    physicalCoverFieldMap (ρp (integerPartial 0 holdoutSource)) =\n'
        f'      {dA_cov} := by\n'
        + partial_value_proof('cover_holdoutSource_partial', sp.expand(dA)) + '\n'
        'theorem cover_physical_companion_partial_value :\n'
        '    physicalCoverFieldMap (ρp (integerPartial 0 holdoutCompanion)) =\n'
        f'      {dC_cov} := by\n'
        + partial_value_proof('cover_holdoutCompanion_partial', sp.expand(dC)))
    # quotient source values
    sub('CoverSourceBinding.lean',
        'theorem cover_quotient_source_value :\n'
        '    quotientCoverFieldMap (ρq coverQuotientSource) =\n'
        '      coverX0^3*(coverY^2+coverT^2)/(2*coverAlpha^2) := by\n'
        '  simp only [coverQuotientSource, scaledCoverQuotientSource, map_mul, map_pow,\n'
        '    quotientCoverFieldMap_residue_X, quotientCoverFieldMap_residue_C,\n'
        '    map_div₀, map_one, map_ofNat]\n'
        '  change (1/(2*coverAlpha^2))*coverX0^3*(coverY^2+coverT^2) = _\n'
        '  ring\n',
        'theorem cover_quotient_source_value :\n'
        '    quotientCoverFieldMap (ρq coverQuotientSource) =\n'
        f'      {B_cov} := by\n'
        '  simp only [coverQuotientSource, scaledCoverQuotientSource, map_mul, map_pow,\n'
        '    quotientCoverFieldMap_residue_X, quotientCoverFieldMap_residue_C,\n'
        '    map_div₀, map_one, map_ofNat, map_neg]\n'
        f'  change ({coef_c})*{qmono_cover} = _\n'
        '  ring\n')
    if dq is None:
        qpartial_proof = ('  unfold coverQuotientSource\n'
                          '  rw [scaledCoverQuotientSource_partial, map_zero, map_zero]\n')
    else:
        c0, dmon = dq
        pre = f'{c0}*' if c0 > 1 else ''
        qpartial_proof = ('  unfold coverQuotientSource\n'
                          '  rw [scaledCoverQuotientSource_partial]\n'
                          '  simp only [map_mul, map_pow, map_ofNat, quotientCoverFieldMap_residue_X,\n'
                          '    quotientCoverFieldMap_residue_C, map_div₀, map_one, map_neg]\n'
                          f'  change {pre}({coef_c})*{mono5(dmon, cover5)} = _\n'
                          '  ring\n')
    sub('CoverSourceBinding.lean',
        'theorem cover_quotient_source_partial_value :\n'
        '    quotientCoverFieldMap (ρq (integerPartial 0 coverQuotientSource)) =\n'
        '      3*coverX0^2*(coverY^2+coverT^2)/(2*coverAlpha^2) := by\n'
        '  unfold coverQuotientSource\n'
        '  rw [scaledCoverQuotientSource_partial]\n'
        '  simp only [map_mul, map_pow, map_ofNat, quotientCoverFieldMap_residue_X,\n'
        '    quotientCoverFieldMap_residue_C, map_div₀, map_one]\n'
        '  change 3*(1/(2*coverAlpha^2))*coverX0^2*(coverY^2+coverT^2) = _\n'
        '  ring\n',
        'theorem cover_quotient_source_partial_value :\n'
        '    quotientCoverFieldMap (ρq (integerPartial 0 coverQuotientSource)) =\n'
        f'      {dB_cov} := by\n' + qpartial_proof)
    # bindings
    sub('CoverSourceBinding.lean',
        '''theorem cover_source_binding :
    (2*coverAlpha^5*(coverT^2-coverY^2)/coverT) *
      quotientCoverFieldMap (ρq coverQuotientSource) =
      physicalCoverFieldMap (ρp holdoutSource) *
        (1-physicalCoverFieldMap (ρp (X 4))^4*(coverT^4)⁻¹) := by
  rw [cover_quotient_source_value, cover_physical_source_value]
  have hy : physicalCoverFieldMap (ρp (X 4)) = coverY := physicalCoverFieldMap_residue_X 4
  rw [hy]
  simpa only [div_eq_mul_inv] using
    cover_source_identity coverAlpha coverX0 coverY coverT coverAlpha_ne_zero coverT_ne_zero
''',
        f'''theorem cover_source_binding :
    (2*coverAlpha^5*(coverT^2-coverY^2)/coverT) *
      quotientCoverFieldMap (ρq coverQuotientSource) =
      physicalCoverFieldMap (ρp holdoutSource) -
        physicalCoverFieldMap (ρp holdoutCompanion) * {E_cover} := by
  rw [cover_quotient_source_value, cover_physical_source_value, cover_physical_companion_value]
  simpa only [div_eq_mul_inv] using
    cover_source_identity {cover_args} coverAlpha_ne_zero coverT_ne_zero
''')
    sub('CoverSourceBinding.lean',
        '''      physicalCoverFieldMap
        ((ρp (integerPartial 0 holdoutSource)*ρp (integerPartial 0 F)-
          ρp holdoutSource*ρp (integerPartial 0 (integerPartial 0 F))) /
            (ρp (integerPartial 0 F))^2) *
        (1-physicalCoverFieldMap (ρp (X 4))^4*(coverT^4)⁻¹) := by
  simp only [map_div₀, map_sub, map_mul, map_pow]
  rw [cover_normal_binding, cover_second_normal_binding,
    cover_quotient_source_partial_value, cover_quotient_source_value,
    cover_physical_source_partial_value, cover_physical_source_value]
  have hy : physicalCoverFieldMap (ρp (X 4)) = coverY := physicalCoverFieldMap_residue_X 4
  rw [hy]
  simpa only [div_eq_mul_inv] using
    cover_normal_source_identity coverAlpha coverX0 coverY coverT
      (physicalCoverFieldMap (ρp (integerPartial 0 F)))
      (physicalCoverFieldMap (ρp (integerPartial 0 (integerPartial 0 F))))
      coverAlpha_ne_zero coverT_ne_zero
''',
        f'''      physicalCoverFieldMap
        ((ρp (integerPartial 0 holdoutSource)*ρp (integerPartial 0 F)-
          ρp holdoutSource*ρp (integerPartial 0 (integerPartial 0 F))) /
            (ρp (integerPartial 0 F))^2) -
      physicalCoverFieldMap
        ((ρp (integerPartial 0 holdoutCompanion)*ρp (integerPartial 0 F)-
          ρp holdoutCompanion*ρp (integerPartial 0 (integerPartial 0 F))) /
            (ρp (integerPartial 0 F))^2) * {E_cover} := by
  simp only [map_div₀, map_sub, map_mul, map_pow]
  rw [cover_normal_binding, cover_second_normal_binding,
    cover_quotient_source_partial_value, cover_quotient_source_value,
    cover_physical_source_partial_value, cover_physical_source_value,
    cover_physical_companion_partial_value, cover_physical_companion_value]
  simpa only [div_eq_mul_inv] using
    cover_normal_source_identity {cover_args}
      (physicalCoverFieldMap (ρp (integerPartial 0 F)))
      (physicalCoverFieldMap (ρp (integerPartial 0 (integerPartial 0 F))))
      coverAlpha_ne_zero coverT_ne_zero
''')
    files['CoverSourceBinding.lean'] = credit + files['CoverSourceBinding.lean']

    # Solution.lean: unchanged apart from the credit header
    files['Solution.lean'] = credit + files['Solution.lean']

    out = OUT / instance
    if out.exists():
        shutil.rmtree(out)
    out.mkdir(parents=True)
    for name, text in files.items():
        (out / name).write_text(text)
    (out / 'proof.json').write_text(
        '{\n  "schemaVersion": 2,\n  "instanceId": "%s",\n  "theorem": "Submission.certificate"\n}\n' % instance)
    (out / 'solution.md').write_text(solution_md(instance, A, C, BSP, k, ekind, epow, trace_lemma))
    summary = dict(instance=instance, A=str(A), companion=str(C), k=k, E=E_cover,
                   quotient_source=str(BSP), coef=coef_f)
    return summary


def latex6(expr):
    return sp.latex(expr, mul_symbol=None).replace('X_{0}', 'X_0').replace('X_{1}', 'X_1').replace('X_{2}', 'X_2') \
        .replace('Y_{0}', 'Y_0').replace('Y_{1}', 'Y_1').replace('Y_{2}', 'Y_2')


def solution_md(instance, A, C, BSP, k, ekind, epow, trace_lemma):
    alpha, beta = sp.symbols('alpha beta')
    Btex = sp.latex(BSP.subs({a: alpha, b: beta, x0: sp.Symbol('X_0'), x1: sp.Symbol('X_1'), x2: sp.Symbol('X_2')}))
    Atex, Ctex = latex6(A), latex6(C)
    if ekind == 'inv':
        Etex = f'T^{{-{epow}}}'
        companion_tex = f'A\\,(y/T)^{{{k}}}=({Ctex})\\,T^{{-{epow}}}'
        trace_tex = f'\\operatorname{{tr}}\\bigl(T^{{-{epow}}}\\bigr)=0'
    else:
        Etex = f'T^{{{epow}}}'
        companion_tex = f'A\\,(y/T)^{{{k}}}=({Ctex})\\,T^{{{epow}}}'
        trace_tex = f'\\operatorname{{tr}}\\bigl(T^{{{epow}}}\\bigr)=0'
    return f'''# A certificate for `{instance}` from the holdout Fermat cover and moving conic

This submission proves the exact existential `HodgeComputer.HasCertificate` statement for the
protected instance `{instance}`, with \\((F,q,A)\\) unchanged:

\\[
F=X_0^6+X_1^6+X_2^6+Y_0^6+Y_1^6+Y_2^6+X_0^3X_1Y_0Y_1+X_1^3X_2Y_1Y_2,\\qquad
A={Atex},\\qquad q=1 .
\\]

It is a direct adaptation of the accepted [holdout solution](../holdout/solution.md) by `fqlx`
(hodge-computer/sextics PR #128). That construction solves the residue equation on the weighted
quotient of a Fermat-curve cover for *every* polynomial source, and its clearing, trace and
homogeneous-extraction steps never depend on the target. Only two steps are target-specific: the
quotient source obtained from \\(A\\), and the deck-trace removal of the reflected companion.
Those two steps are replaced here; every other module is reused verbatim with its original
attribution. No expanded denominator or numerical degree is listed; the proof is existential, as
the [formal contract](../../formal/README.md) allows.

## 1. The cover, the quotient, and the source

As in the holdout solution, adjoin \\(T\\) with \\(T^6=Y_0^6+Y_2^6\\), put
\\(\\alpha=Y_0/T\\), \\(\\beta=Y_2/T\\), \\(y=Y_1\\), so that \\(\\alpha^6+\\beta^6=1\\), and use the
interchange-invariant coordinates \\(S=y^2+T^2\\), \\(P=yT\\). The quotient hypersurface is

\\[
H=X_0^6+X_1^6+X_2^6+P(\\alpha X_0^3X_1+\\beta X_1^3X_2)+S^3-3SP^2
\\]

in the coordinate order \\((X_0,X_1,X_2,S,P)\\) with weights \\((1,1,1,2,2)\\).

The pulled-back density of the target is \\(A\\cdot(-T/\\alpha^5)\\) in the cover order
\\((X_0,X_1,X_2,y,T,\\beta)\\). Adding its image under the interchange \\(y\\leftrightarrow T\\)
(determinant \\(-1\\)) and dividing by \\(\\det\\partial(S,P)/\\partial(y,T)=2(y^2-T^2)\\) gives the
polynomial quotient source

\\[
B={Btex}\\in K_b[X_0,X_1,X_2,S,P],
\\]

of weighted degree five, as required for pole order two on \\(H\\). Exactly as in the accepted
proof, the five-coordinate Jacobian \\(J_c=2\\alpha^5(T^2-y^2)/T\\) satisfies the exact identity

\\[
J_c\\,B=A-{companion_tex},
\\]

where the second term is the reflected companion \\(A\\,(y/T)^{{k}}\\) with
\\(k=b_0+b_2+1-b_1={k}\\) for the exponents \\((b_0,b_1,b_2)\\) of \\((Y_0,Y_1,Y_2)\\) in \\(A\\).
The same identity holds for the distinguished normal-divergence sources, because \\(J_c\\), \\(y\\)
and \\(T\\) are independent of \\(X_0\\). Both identities are proved as universal field identities
(`cover_source_identity`, `cover_normal_source_identity`) and then bound to the actual residue
function fields (`cover_source_binding`, `cover_normal_source_binding`).

## 2. The deck trace

The companion is a physical polynomial \\({Ctex}\\) times \\({Etex}\\). The common cover has the deck
automorphism \\(T\\mapsto\\zeta T\\), \\(\\alpha\\mapsto\\zeta^{{-1}}\\alpha\\), \\(\\beta\\mapsto\\zeta^{{-1}}\\beta\\)
fixing every physical coordinate, so \\({Etex}\\) is an eigenvector with eigenvalue
\\(\\zeta^{{{-epow if ekind == 'inv' else epow}}}\\). Choosing \\(\\zeta\\) a primitive cube root of unity makes this eigenvalue
different from one, hence \\({trace_tex}\\) for the normalized trace to the physical function field
(`{trace_lemma}`, from the eigencharacter lemma `normalizedTrace_eigen_zero`). Linearity of the
normalized trace over the physical field then recovers exactly the source \\(A\\)
(`physical_normal_source_trace`). This is the only place where the sign and exponent of the
companion matter; it replaces the \\(T^{{-4}}\\) trace used for the central cubic.

## 3. Everything else is the accepted construction

The exact conic seed, the étale coefficient algebra, the finite family through the generic point,
the polynomial normal vector, the polynomial integration of the residue equation
(`conic_target_residue_solution`, applied to the source \\(B\\) above), the finite trace descent,
the physical transport (`holdout_hasCertificate_of_quotient_divergence`), legal polynomial
clearing, and the finite homogeneous extraction are the unchanged modules of PR #128. In
particular the residue solution theorem is stated for an arbitrary polynomial source, so no new
conic or seed is needed. Smoothness-type side conditions (nonvanishing of the distinguished
derivatives, irreducibility of \\(F\\) and \\(H\\), nonvanishing of \\(\\alpha\\) and \\(T\\)) are the
accepted ones.

The closed wrapper [Solution.lean](Solution.lean) proves

```lean
theorem Submission.certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q
```

by selecting the checked complex seed, applying `conic_target_residue_solution` to
`coverQuotientSource`, and invoking `holdout_hasCertificate_of_quotient_divergence`. It uses
only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.

## 4. Correspondence with the Lean sources

| Step | Declarations (modified modules) |
| --- | --- |
| Protected numerator and companion polynomial | [HomogeneousCertificate.lean](HomogeneousCertificate.lean): `holdoutSource`, `holdoutCompanion`, `holdoutSource_isHomogeneous` |
| Scalar source identities, Section 1 | [CoverScalars.lean](CoverScalars.lean): `cover_source_identity`, `cover_normal_source_identity` |
| Quotient source and its bindings | [CoverSourceBinding.lean](CoverSourceBinding.lean): `coverQuotientSource`, `cover_source_binding`, `cover_normal_source_binding` |
| Deck eigencharacters and trace, Section 2 | [DeckTrace.lean](DeckTrace.lean): `normalizedTrace_inv_pow_zero`, `normalizedTrace_pow_zero`; [CoverDeckField.lean](CoverDeckField.lean): `exists_nontrivial_sixth_root`, `{trace_lemma}` |
| Closure with a trace-free companion | [HoldoutCertificateClosure.lean](HoldoutCertificateClosure.lean): `physicalCompanionNormalSource`, `holdout_hasCertificate_of_cover_residue`; [CoverCertificate.lean](CoverCertificate.lean): `holdout_hasCertificate_of_quotient_divergence` |

All other modules are byte-for-byte copies of the accepted holdout sources apart from a header
comment recording this adaptation.

## 5. Context and attribution

- **`fqlx`** constructed the Fermat cover, the moving conic, the finite-algebra residue solution,
  and the complete Lean development in [PR #128](https://github.com/hodge-computer/sextics/pull/128),
  with disclosed **OpenAI ChatGPT** assistance; that proof credits `HeadOfNaps`'s fraction-derivation
  construction ([PR #122](https://github.com/hodge-computer/sextics/pull/122)), the hidden-reflection
  observations of `fringewidth`, and the earlier holdout analysis of `rbajaj5`. This submission is
  that construction with its two target-specific steps replaced.
- **The repository authors, including Benjamin E. Diamond**, supplied the certificate formalism, the
  residue interpretation and the normalization used throughout; the geometric meaning follows
  Griffiths's residue theory and Diamond's certificate correspondence.
- The source-agnostic reading of the construction, the per-target quotient sources and deck
  exponents, and the Lean adaptation were prepared with **Claude Code** assistance for a
  contribution through GitHub account `DiamondJM`; the per-target identities were checked
  independently with sympy. Kernel verification establishes the formal claim; no independent human
  review is asserted.
'''


if __name__ == '__main__':
    for inst, exps in TARGETS.items():
        if ONLY and inst not in ONLY:
            continue
        s = build(inst, exps)
        print(s)
