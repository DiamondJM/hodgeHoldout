## Contribution

Solve of `one-reflection-y2-sector`: the theorem `Submission.certificate` in `data/one-reflection-y2-sector/Solution.lean` proves the protected statement `HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q` for the unchanged instance ($A=X_0^3Y_0Y_1Y_2$, $q=1$, $F=F_0+X_0^3X_1Y_0Y_1+X_1^3X_2Y_0Y_1$).

## Mathematics

Existence proof, no expanded witness. Nonconstructive existence was known from the reflection theorem (the sextic is even in $Y_2$, the target odd); this PR supplies a finite algebraic existence proof checked by Lean. It adapts `fqlx`'s accepted holdout construction (PR #128): both couplings of $F$ contain $Y_0Y_1$, so the same Fermat cover $(Y_0,Y_1,Y_2)=(\alpha T,y,\beta T)$ applies and its reflection quotient is the holdout quotient $H(\alpha,\beta)$ with both coupling coefficients equal to $\alpha$. The new input is the conic seed: `fqlx`'s conic family lies on $H(\alpha_c,\beta_c)$ for every parameter $r$, and imposing $\beta_c=\alpha_c$ singles out the roots of the integer polynomial $g(r)=r^8+7r^7-58r^6+149r^5-178r^4+115r^3-44r^2+10r-1$, which has a root in $(-13,-12)$ where all auxiliary quantities and both Jacobian polynomials are sign-definite. The target data are $B=\beta X_0^3P/(2\alpha^4)$ with deck exponent $k=2$. Details and the module correspondence are in [`data/one-reflection-y2-sector/solution.md`](https://github.com/DiamondJM/sextics/blob/solve/one-reflection-y2-sector/data/one-reflection-y2-sector/solution.md).

Prior results and collaborators: `fqlx` (the cover, moving conic, finite-algebra residue solution and the Lean development, with OpenAI ChatGPT assistance; attribution retained in every reused module), `HeadOfNaps` (fraction-derivation construction credited inside that proof), `fringewidth` (hidden reflections of this sextic), and the repository authors including Benjamin E. Diamond (certificate framework and reflection theorem). Prepared with Claude Code assistance for `DiamondJM`; the seed and the scalar identities were checked independently with sympy and mpmath.

## Verification

- `python3 scripts/proposals/check-explanation.py --instance one-reflection-y2-sector`: passed.
- The modules were compiled against the pinned toolchain (Lean 4.33.0, committed Lake manifest) in the verifier's module order with `HodgeTarget.lean` generated from `instance.rec` and `HodgeChecked.lean` checking the exact theorem: all 59 modules compiled. The repository's own `sandbox.verify` (Docker, no network) then replayed every module with `leanchecker` and audited the theorem: `kernelReplay: true`, axioms `propext`, `Quot.sound`, `Classical.choice`. Run: https://github.com/DiamondJM/hodgeHoldout/actions/runs/39308766798. These were run on a GitHub-hosted runner outside this repository, so **Lean acceptance relies on the protected CI of this repository**.
- No witness JSON is supplied.

For a solve:

- [x] Only permitted new files in one existing `data/one-reflection-y2-sector/` folder are added.
- [x] `proof.json`, `Solution.lean`, and `solution.md` are present; the other files are flat Lean helpers.
- [x] The theorem proves the fixed protected statement without placeholders or unapproved axioms.
- [x] No JSON witness is supplied, so no witness binding applies.
- [x] Existing target, context, verifier, website, and generated files are unchanged.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01Ra7gCpqbrEyKu1FqgWh9iL
