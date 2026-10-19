# A certificate for `holdout-x12-p-y02` from the holdout Fermat cover and moving conic

This submission proves the exact existential `HodgeComputer.HasCertificate` statement for the
protected instance `holdout-x12-p-y02`, with \((F,q,A)\) unchanged:

\[
F=X_0^6+X_1^6+X_2^6+Y_0^6+Y_1^6+Y_2^6+X_0^3X_1Y_0Y_1+X_1^3X_2Y_1Y_2,\qquad
A=X_1^{2} X_2 Y_0^{2} Y_2,\qquad q=1 .
\]

It is a direct adaptation of the accepted [holdout solution](../holdout/solution.md) by `fqlx`
(hodge-computer/sextics PR #128). That construction solves the residue equation on the weighted
quotient of a Fermat-curve cover for *every* polynomial source, and its clearing, trace and
homogeneous-extraction steps never depend on the target. Only two steps are target-specific: the
quotient source obtained from \(A\), and the deck-trace removal of the reflected companion.
Those two steps are replaced here; every other module is reused verbatim with its original
attribution. No expanded denominator or numerical degree is listed; the proof is existential, as
the [formal contract](../../formal/README.md) allows.

## 1. The cover, the quotient, and the source

As in the holdout solution, adjoin \(T\) with \(T^6=Y_0^6+Y_2^6\), put
\(\alpha=Y_0/T\), \(\beta=Y_2/T\), \(y=Y_1\), so that \(\alpha^6+\beta^6=1\), and use the
interchange-invariant coordinates \(S=y^2+T^2\), \(P=yT\). The quotient hypersurface is

\[
H=X_0^6+X_1^6+X_2^6+P(\alpha X_0^3X_1+\beta X_1^3X_2)+S^3-3SP^2
\]

in the coordinate order \((X_0,X_1,X_2,S,P)\) with weights \((1,1,1,2,2)\).

The pulled-back density of the target is \(A\cdot(-T/\alpha^5)\) in the cover order
\((X_0,X_1,X_2,y,T,\beta)\). Adding its image under the interchange \(y\leftrightarrow T\)
(determinant \(-1\)) and dividing by \(\det\partial(S,P)/\partial(y,T)=2(y^2-T^2)\) gives the
polynomial quotient source

\[
B=\frac{S X_{1}^{2} X_{2} \beta}{2 \alpha^{3}}\in K_b[X_0,X_1,X_2,S,P],
\]

of weighted degree five, as required for pole order two on \(H\). Exactly as in the accepted
proof, the five-coordinate Jacobian \(J_c=2\alpha^5(T^2-y^2)/T\) satisfies the exact identity

\[
J_c\,B=A-A\,(y/T)^{4}=(X_1^{2} X_2 Y_0^{2} Y_1^{4} Y_2)\,T^{-4},
\]

where the second term is the reflected companion \(A\,(y/T)^{k}\) with
\(k=b_0+b_2+1-b_1=4\) for the exponents \((b_0,b_1,b_2)\) of \((Y_0,Y_1,Y_2)\) in \(A\).
The same identity holds for the distinguished normal-divergence sources, because \(J_c\), \(y\)
and \(T\) are independent of \(X_0\). Both identities are proved as universal field identities
(`cover_source_identity`, `cover_normal_source_identity`) and then bound to the actual residue
function fields (`cover_source_binding`, `cover_normal_source_binding`).

## 2. The deck trace

The companion is a physical polynomial \(X_1^{2} X_2 Y_0^{2} Y_1^{4} Y_2\) times \(T^{-4}\). The common cover has the deck
automorphism \(T\mapsto\zeta T\), \(\alpha\mapsto\zeta^{-1}\alpha\), \(\beta\mapsto\zeta^{-1}\beta\)
fixing every physical coordinate, so \(T^{-4}\) is an eigenvector with eigenvalue
\(\zeta^{-4}\). Choosing \(\zeta\) a primitive cube root of unity makes this eigenvalue
different from one, hence \(\operatorname{tr}\bigl(T^{-4}\bigr)=0\) for the normalized trace to the physical function field
(`commonCover_trace_inverse_fourth`, from the eigencharacter lemma `normalizedTrace_eigen_zero`). Linearity of the
normalized trace over the physical field then recovers exactly the source \(A\)
(`physical_normal_source_trace`). This is the only place where the sign and exponent of the
companion matter; it replaces the \(T^{-4}\) trace used for the central cubic.

## 3. Everything else is the accepted construction

The exact conic seed, the étale coefficient algebra, the finite family through the generic point,
the polynomial normal vector, the polynomial integration of the residue equation
(`conic_target_residue_solution`, applied to the source \(B\) above), the finite trace descent,
the physical transport (`holdout_hasCertificate_of_quotient_divergence`), legal polynomial
clearing, and the finite homogeneous extraction are the unchanged modules of PR #128. In
particular the residue solution theorem is stated for an arbitrary polynomial source, so no new
conic or seed is needed. Smoothness-type side conditions (nonvanishing of the distinguished
derivatives, irreducibility of \(F\) and \(H\), nonvanishing of \(\alpha\) and \(T\)) are the
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
| Deck eigencharacters and trace, Section 2 | [DeckTrace.lean](DeckTrace.lean): `normalizedTrace_inv_pow_zero`, `normalizedTrace_pow_zero`; [CoverDeckField.lean](CoverDeckField.lean): `exists_nontrivial_sixth_root`, `commonCover_trace_inverse_fourth` |
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
