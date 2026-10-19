#!/usr/bin/env python3
"""Derive the proposal folder for `one-reflection-y2-sector` from fqlx's accepted holdout proof.

The one-reflection sextic F = Fermat + Y0*Y1*(X0^3*X1 + X1^3*X2) admits the same Fermat cover
(Y0, Y1, Y2) = (alpha*T, y, beta*T); its quotient is the holdout quotient H(alpha, beta) with both
coupling coefficients equal to alpha. The adaptation therefore (i) aliases the quotient-side
coefficient beta to alpha, (ii) replaces the coupling coefficient on the cover side, (iii) swaps
the physical sextic, (iv) installs a new conic seed (a member of fqlx's family with beta = alpha),
and (v) supplies the target data for A = X0^3*Y0*Y1*Y2 through the holdout-target generator.

Usage: gen_oneref.py SEXTICS_ROOT OUT_ROOT
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.argv = [sys.argv[0], sys.argv[1], sys.argv[2]]
import gen_holdout_targets as G  # noqa: E402

INSTANCE = 'one-reflection-y2-sector'
out = Path(sys.argv[2]) / INSTANCE
G.build(INSTANCE, (3, 0, 0, 1, 1, 1))


def edit(name, pairs, regex=False):
    p = out / name
    text = p.read_text()
    for old, new, count in pairs:
        if regex:
            text, n = re.subn(old, new, text)
        else:
            n = text.count(old)
            text = text.replace(old, new)
        assert (count is None and n > 0) or n == count, (name, old[:70], n, count)
    p.write_text(text)


PAIR_C = '(genericBaseAlpha ℂ) (genericBaseBeta ℂ)'
PAIR_C_NEW = '(genericBaseAlpha ℂ) (genericBaseAlpha ℂ)'
PAIR_K = '(genericBaseAlpha K) (genericBaseBeta K)'
PAIR_K_NEW = '(genericBaseAlpha K) (genericBaseAlpha K)'

# (iii) the physical sextic
edit('HypersurfaceCoordinates.lean', [
    ('MvPolynomial.X 0^3 * MvPolynomial.X 1 * MvPolynomial.X 3 * MvPolynomial.X 4))',
     'MvPolynomial.X 0^3 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3))', 1),
    ('MvPolynomial.X 1^6 + MvPolynomial.X 1^3*MvPolynomial.X 2*MvPolynomial.X 4*MvPolynomial.X 5 +',
     'MvPolynomial.X 1^6 + MvPolynomial.X 1^3*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 4 +', 1),
    ('The exact holdout sextic, monic in `X0`.', 'The exact one-reflection sextic, monic in `X0`.', 1),
])
edit('HomogeneousCertificate.lean', [('(hc 1 2 4 5)', '(hc 1 2 3 4)', 1)])

# (ii) the coupling coefficient on the cover side
edit('PhysicalCoverEmbedding.lean', [
    ('(baseAlpha (R := K)) (baseBeta (R := K))', '(baseAlpha (R := K)) (baseAlpha (R := K))', None)])
edit('CommonCoverBaseChange.lean', [
    (PAIR_K, PAIR_K_NEW, None), ('baseAlpha baseBeta', 'baseAlpha baseAlpha', None)])
edit('CoverCoordinates.lean', [('      baseAlpha baseBeta\n', '      baseAlpha baseAlpha\n', 1)])
for name in ('CoverFields.lean', 'CoverCoordinates.lean', 'QuotientCoverField.lean',
             'CoverQuotientCompatibility.lean', 'CoverSourceBinding.lean', 'CoverCertificate.lean'):
    edit(name, [(PAIR_C, PAIR_C_NEW, None)])
edit('FermatDeck.lean', [
    (PAIR_K, PAIR_K_NEW, None),
    ('      C (MvPolynomial.X 3))*hcb + C (MvPolynomial.X 3)^6*hcc',
     '      C (MvPolynomial.X 3))*hca + C (MvPolynomial.X 3)^6*hcc', 1)])

# (iv) the seed
(out / 'CurveSeed.lean').write_text((HERE / 'oneref' / 'CurveSeed.lean').read_text())
edit('CurveSeedIncidence.lean', [
    ('ne_of_gt (HoldoutConic.gEven_pos p.lower)', 'HoldoutConic.gEven_ne_zero p.upper', 1),
    ('ne_of_gt (HoldoutConic.gOdd_pos p.lower)', 'HoldoutConic.gOdd_ne_zero p.upper', 1),
    ('p.lower', 'p.upper', None),
    ('theorem seed_V (p : HoldoutConic.Seed) :\n'
     '    (p.beta*p.k^3)*p.q = 3*(1-2*(p.r : ℂ)) := by\n'
     '  have h : (p.beta*p.k^3)*p.q = (HoldoutConic.b p.r : ℂ) := by\n',
     'theorem seed_V (p : HoldoutConic.Seed) :\n'
     '    (p.alpha*p.k^3)*p.q = 3*(1-2*(p.r : ℂ)) := by\n'
     '  rw [← p.beta_eq_alpha]\n'
     '  have h : (p.beta*p.k^3)*p.q = (HoldoutConic.b p.r : ℂ) := by\n', 1),
])
# every remaining p.beta is a coupling coefficient of H: it becomes p.alpha
edit('CurveSeedIncidence.lean', [
    (r'p\.beta(?!_eq_alpha)', 'p.alpha', None)], regex=True)
# the seed_V proof body must keep its two Seed.beta references
txt = (out / 'CurveSeedIncidence.lean').read_text()
txt = txt.replace(
    '  rw [← p.beta_eq_alpha]\n  have h : (p.alpha*p.k^3)*p.q = (HoldoutConic.b p.r : ℂ) := by\n',
    '  rw [← p.beta_eq_alpha]\n  have h : (p.beta*p.k^3)*p.q = (HoldoutConic.b p.r : ℂ) := by\n')
assert 'unfold HoldoutConic.Seed.beta' in txt
(out / 'CurveSeedIncidence.lean').write_text(txt)

# (i) alias the quotient-side beta to alpha
edit('FermatIncidenceSeed.lean', [
    ('def fermatBeta : FermatEndpointRing :=\n  algebraMap FermatCurveBase FermatEndpointRing baseBeta',
     'def fermatBeta : FermatEndpointRing :=\n  algebraMap FermatCurveBase FermatEndpointRing baseAlpha', 1),
    ('(baseEval p.alpha p.beta p.base_relation)', '(baseEval p.alpha p.baseBeta p.base_relation)', 1),
    ('    fermatSeedEval p fermatBeta = p.beta := by', '    fermatSeedEval p fermatBeta = p.alpha := by', 1),
])
edit('ConicEmbedding.lean', [
    ('def genericBeta : FermatBaseField := algebraMap FermatCurveBase FermatBaseField baseBeta',
     'def genericBeta : FermatBaseField := algebraMap FermatCurveBase FermatBaseField baseAlpha', 1),
    ('  have h := conicCurve_equation p\n', '  have h := conicCurve_equation p\n  rw [conicAlpha_base, conicBeta_base] at h\n', 1),
    ('    ← conicAlpha_base, ← conicBeta_base,\n', '', 1),
])
edit('ConicPolynomialFamily.lean', [
    (r'(theorem conicBeta_base \(p : HoldoutConic\.Seed\) :\n    conicBeta p = algebraMap FermatBaseField \(ConicCoefficientField p\)\n'
     r'      \(algebraMap FermatCurveBase FermatBaseField )baseBeta(\) :=\n  conicSourceMap_base p )baseBeta',
     r'\1baseAlpha\2baseAlpha', 1)], regex=True)
edit('ConicResidue.lean', [
    ('  rw [← conicAlpha_base, ← conicBeta_base]', '  rw [conicAlpha_base, conicBeta_base]', 1)])

# manifest and explanation
(out / 'proof.json').write_text('{\n  "schemaVersion": 2,\n  "instanceId": "%s",\n  "theorem": "Submission.certificate"\n}\n' % INSTANCE)
(out / 'solution.md').write_text(r'''# A certificate for `one-reflection-y2-sector` from a Fermat cover and a moving conic

This submission proves the exact existential `HodgeComputer.HasCertificate` statement for the
protected instance `one-reflection-y2-sector`, with \((F,q,A)\) unchanged:

\[
F=X_0^6+X_1^6+X_2^6+Y_0^6+Y_1^6+Y_2^6+X_0^3X_1Y_0Y_1+X_1^3X_2Y_0Y_1,\qquad
A=X_0^3Y_0Y_1Y_2,\qquad q=1 .
\]

Nonconstructive existence was already known from the reflection theorem of the book (the sextic
is even in \(Y_2\) and the target is odd in it). What is supplied here is a finite algebraic
existence proof checked by Lean, obtained by adapting the accepted
[holdout solution](../holdout/solution.md) of `fqlx` (hodge-computer/sextics PR #128).

## 1. The same cover, a specialised quotient

Both couplings of \(F\) contain the factor \(Y_0Y_1\). Adjoin \(T\) with \(T^6=Y_0^6+Y_2^6\) and put
\(\alpha=Y_0/T\), \(\beta=Y_2/T\), \(y=Y_1\), so that \(\alpha^6+\beta^6=1\). On this cover

\[
G=X_0^6+X_1^6+X_2^6+y^6+T^6+\alpha\,yT\,(X_0^3X_1+X_1^3X_2),
\]

which is invariant under the interchange \(y\leftrightarrow T\). With \(S=y^2+T^2\), \(P=yT\) the
quotient is

\[
H=X_0^6+X_1^6+X_2^6+\alpha P\,(X_0^3X_1+X_1^3X_2)+S^3-3SP^2,
\]

that is, the holdout quotient \(H(\alpha,\beta)\) of PR #128 with both coupling coefficients equal
to \(\alpha\). In the Lean sources this is expressed by using `weightedHypersurface alpha alpha`
and `commonCoverPolynomial alpha alpha` on the quotient and cover sides; the coefficient field is
still the function field of the Fermat curve, because the cover coordinate \(\beta\) is needed
for \(Y_2\). The modules handling the generic conic family, the étale coefficient algebra, the
polynomial normal vector, the polynomial integration of the residue equation, finite trace
descent, legal clearing and homogeneous extraction are reused with their original attribution.

## 2. The conic seed on the equal-coefficient quotient

`fqlx`'s conic (equations (8)–(10) of the holdout write-up) lies on \(H(\alpha_c,\beta_c)\) for
*every* value of its parameter \(r\); the degree-23 polynomial there only enforces the Fermat
relation between the two coefficients. Here the two coefficients must coincide instead:
\(\beta_c=\alpha_c\) is equivalent to \(k_c^2=1-r\), and with \(q_c^2=M/(1-r)^3\) the relation
\(q_c^4=R\) becomes the integer polynomial

\[
g(r)=r^8+7r^7-58r^6+149r^5-178r^4+115r^3-44r^2+10r-1 ,
\]

which has a root in \((-13,-12)\) by the intermediate value theorem
(\(g(-13)=35869443\), \(g(-12)=-35000185\)). For \(r<-12\) the auxiliary quantities
\(m,R,M,a,b\) are positive, \(1-r\) is positive, and both Jacobian polynomials
\(g_{\rm even},g_{\rm odd}\) of the accepted proof are negative, each being minus a polynomial in
\(-12-r\) with positive coefficients. Thus the seed is nonsingular exactly as in PR #128
(`gEven_neg`, `gOdd_neg`, `seedJacobian_nonsingular`). The cover coordinate \(\beta\) at the seed
is any sixth root of \(1-\alpha_c^6\) (`Seed.baseBeta`), which puts the seed on the Fermat curve
(`Seed.base_relation`); the curve identity on \(H(\alpha_c,\alpha_c)\) is `Seed.curve`, obtained
from fqlx's identity through `Seed.beta_eq_alpha`.

## 3. Source and deck trace for the target

With \(A=X_0^3Y_0Y_1Y_2\) the pulled-back density, symmetrised under \(y\leftrightarrow T\) and
divided by \(2(y^2-T^2)\), is the weighted-degree-five source

\[
B=\frac{\beta X_0^3P}{2\alpha^4},\qquad
J_c\,B=A-\bigl(X_0^3Y_0Y_1^3Y_2\bigr)\,T^{-2},\qquad J_c=\frac{2\alpha^5(T^2-y^2)}{T}.
\]

The reflected companion is \(A(y/T)^2\); under the deck automorphism \(T\mapsto\zeta T\) fixing
the physical field it is a \(\zeta^{-2}\)-eigenvector, so for a primitive cube root \(\zeta\) its
normalized trace vanishes (`commonCover_trace_inverse_square`). The closure then recovers the
exact source \(A\) and the remaining steps are the accepted ones. The scalar identities are
`cover_source_identity` and `cover_normal_source_identity`; their bindings to the residue fields
are `cover_source_binding` and `cover_normal_source_binding`.

## 4. Correspondence with the Lean sources

| Step | Declarations |
| --- | --- |
| Protected sextic and numerator | [HypersurfaceCoordinates.lean](HypersurfaceCoordinates.lean): `holdoutSextic` (the one-reflection sextic, name kept), `holdoutSextic_irreducible`; [HomogeneousCertificate.lean](HomogeneousCertificate.lean): `holdoutSource`, `holdoutCompanion` |
| Equal-coefficient quotient and cover | [PhysicalCoverEmbedding.lean](PhysicalCoverEmbedding.lean): `holdoutPolynomial_commonCover`; [QuotientCoverField.lean](QuotientCoverField.lean), [CoverQuotientCompatibility.lean](CoverQuotientCompatibility.lean) with `weightedHypersurface alpha alpha`; [FermatIncidenceSeed.lean](FermatIncidenceSeed.lean) and [ConicEmbedding.lean](ConicEmbedding.lean): `fermatBeta`, `genericBeta` aliased to the alpha coefficient |
| Seed, Section 2 | [CurveSeed.lean](CurveSeed.lean): `g`, `exists_parameter`, `gEven_neg`, `gOdd_neg`, `parameter_relation`, `Seed`, `Seed.beta_eq_alpha`, `Seed.base_relation`, `Seed.curve`; [CurveSeedIncidence.lean](CurveSeedIncidence.lean): `seedJacobian_nonsingular` |
| Target data, Section 3 | [CoverScalars.lean](CoverScalars.lean), [CoverSourceBinding.lean](CoverSourceBinding.lean), [CoverDeckField.lean](CoverDeckField.lean), [HoldoutCertificateClosure.lean](HoldoutCertificateClosure.lean), [CoverCertificate.lean](CoverCertificate.lean) |

The closed wrapper [Solution.lean](Solution.lean) proves

```lean
theorem Submission.certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q
```

with only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.

## 5. Context and attribution

- **`fqlx`** constructed the Fermat cover, the moving conic, the finite-algebra residue solution,
  and the complete Lean development in [PR #128](https://github.com/hodge-computer/sextics/pull/128)
  with disclosed **OpenAI ChatGPT** assistance; that proof credits `HeadOfNaps`'s
  fraction-derivation construction ([PR #122](https://github.com/hodge-computer/sextics/pull/122)).
  The conic family and the two Jacobian polynomials used for the new seed are fqlx's.
- `fringewidth` identified the hidden reflections of this sextic in the
  [one-reflection discussion](https://github.com/hodge-computer/sextics/discussions/54), and the
  accepted [one-reflection solution](../one-reflection/solution.md) by `fqlx` gives the explicit
  certificate for the companion target \(X_0^3Y_0^3\) on the same sextic.
- **The repository authors, including Benjamin E. Diamond**, supplied the certificate formalism,
  the reflection theorem that predicts existence for this target, and the residue interpretation
  following Griffiths's residue theory and Diamond's certificate correspondence.
- The specialisation to equal coupling coefficients, the new seed, and the Lean adaptation were
  prepared with **Claude Code** assistance for a contribution through GitHub account `DiamondJM`;
  the seed data and scalar identities were checked independently with sympy and mpmath. Kernel
  verification establishes the formal claim; no independent human review is asserted.
''')
print('wrote', out)
