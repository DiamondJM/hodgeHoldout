#!/usr/bin/env python3
"""Print the solution PR body for one adapted holdout target.

Usage: pr_body.py INSTANCE A_LATEX K COMPILE_RUN_URL
"""
import sys

instance, A, k, run_url = sys.argv[1:5]
print(f'''## Contribution

Solve of `{instance}`: the theorem `Submission.certificate` in `data/{instance}/Solution.lean` proves the protected statement `HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q` for the unchanged instance ($A={A}$, $q=1$, the holdout sextic).

## Mathematics

Existence proof, no expanded witness. The construction is `fqlx`'s accepted holdout proof (PR #128): a Fermat-curve cover, its reflection quotient, and a moving conic on the quotient that solves the residue equation for every polynomial source, followed by finite trace descent, legal clearing and homogeneous extraction. That construction is target-independent except for two steps, which are replaced here: the quotient source obtained from $A$ (now ${{B}}$ of weighted degree five with $k={k}$ for the reflected companion $A(y/T)^k$), and the deck trace that removes the companion (now the trace of $T^{{-k}}$ instead of $T^{{-4}}$). Details, the exact identities, and the module-by-module correspondence are in [`data/{instance}/solution.md`](https://github.com/DiamondJM/sextics/blob/solve/{instance}/data/{instance}/solution.md). The observation that the accepted construction serves all ten remaining basic holdout targets, with the per-target table, is recorded in [discussion #44](https://github.com/hodge-computer/sextics/discussions/44#discussioncomment-19046728).

Prior results and collaborators: `fqlx` (the entire construction and Lean development, with OpenAI ChatGPT assistance, retained as attribution in every module), `HeadOfNaps` (fraction-derivation construction credited inside that proof), `fringewidth` and `rbajaj5` (earlier holdout analysis), and the repository authors including Benjamin E. Diamond (certificate framework). This adaptation was prepared with Claude Code assistance for `DiamondJM`; the per-target scalar identities were checked independently with sympy.

## Verification

- `python3 scripts/proposals/check-explanation.py --instance {instance}`: passed (explanation links and displayed mathematics).
- The Lean modules were compiled against the pinned toolchain (Lean 4.33.0, committed Lake manifest) in the order the verifier uses, with `HodgeTarget.lean` generated from `instance.rec` and `HodgeChecked.lean` checking the exact theorem: all modules compiled, see {run_url}. This was a plain compile on a GitHub-hosted runner, not the sandboxed verifier, so **Lean acceptance relies on the protected CI of this repository**.
- No witness JSON is supplied.

For a solve:

- [x] Only permitted new files in one existing `data/{instance}/` folder are added.
- [x] `proof.json`, `Solution.lean`, and `solution.md` are present; the other files are flat Lean helpers.
- [x] The theorem proves the fixed protected statement without placeholders or unapproved axioms (`propext`, `Classical.choice`, `Quot.sound` only, as in the accepted holdout proof it adapts).
- [x] No JSON witness is supplied, so no witness binding applies.
- [x] Existing target, context, verifier, website, and generated files are unchanged.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01Ra7gCpqbrEyKu1FqgWh9iL''')
