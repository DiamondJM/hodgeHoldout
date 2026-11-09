# four-plus-two-residual: scope (2026-11-09)

F = H(X0,X1,Y0,Y1) + B(X2,Y2), q = 1, A = X0^3 Y0^3.  Existence is argued in prose by the book's
two-reflection theorem (Ch. 3B); no Lean proof and no upstream PR as of this date.

## Reduction to the 4-variable core (transfer.py, core4.py)
A certificate exists iff there is a rational vector field p on C^4, homogeneous of degree 1, with
    p(H) - (3/2) H div p = A.                                                     (*)
Then V = p + (A - p(H))/(6B) (X2 d/dX2 + Y2 d/dY2) has V(F) = A exactly and
A - V(F) + F div V = -(2/3)(A - p(H)) F^2/(H B), so denominator D_p * H * B is legal.
(Derived via the weighted threefold T: H + w^3 = 0, w^3 -> B, w d/dw -> (s d/ds + t d/dt)/2; the
transfer is checked exactly at random rational points.)  This is the homogeneous form of the book's
suspension theorem, section 2.8 (coefficient 5/3 on an affine chart) -- NOT new, found independently.
Euler gauge: p -> p + c E with E(c) = 0 does not change (*).

## Fixed-denominator tests of (*) (core4.py, core4_sweep.py; mod 268435399)
Controls on the split core hX + hY: D = hX solves A = X0^3 X1 Y0^2 (X-degree 4, the join field) and
does not solve A = X0^3 Y0^3.  On the real core:
 * 112 natural denominators of degree 1..12 (monomials, sixth-power sums, hX, hY, coupling, partials
   of H, hX hY): none solvable;
 * 22 denominators H^k * (small factor), k = 1, 2, degree <= 18: none solvable.
Cost: 4 variables, so degree-d systems have 4 C(d+4,3) unknowns; d ~ 35 is feasible here (with the
Y-parity split), far beyond the 6-variable sweep.

## What a solve needs
The support is expected to be the surface swept by a 1-parameter family of the book's genus-four
norm-contact curves on T (3B.2: G = f1 g1 + f2 g2 + A^2 - B^2), of unknown and probably large degree.
A concrete plan:
 1. find one norm-contact presentation of G = H + w^3 (nonlinear system, 90 unknowns, 70 equations;
    the book's cubic-surface-line shortcut needs G = A^2 - B^2 + cubic(q0..q3));
 2. follow its 1-parameter family and eliminate to get the swept surface's image D in P^3;
 3. run the linear test (*) with that D (and its sigma-translate); if solvable, p is explicit, and the
    certificate is an explicit polynomial identity that Lean can check directly (as in one-reflection).
The book's own route (2.8 moving-point currents) needs a core that is even in one variable, which
this core is not; the maintainers' open PRs (#222, #223) target symmetric-sextic-residual instead.
Risks: step 1-2 may give a surface of degree > 35 (then the linear test is out of reach here);
the support may need several families; and the maintainers may solve it first with their machinery.

## Step 1 result (normcontact.py, nc_count.py) -- 2026-11-09
After u = q(x) the presentation is  H + q^3 = h sigma(h) + Q M  (q, Q even quadrics, h cubic, M even
quartic); with the gauge fixed it is 44 equations in 44 unknowns.  Complex Newton from random starts
converges in ~80% of trials to non-degenerate solutions (residual 1e-14, Jacobian nonsingular, Q of
rank 4): norm-contact curves exist on this exact core.
But: 3065 converged starts at one value of the family parameter gave 3065 DISTINCT solutions, no repeat.
So the parameter curve has more than ~1.5 million sheets over the gauge parameter (birthday bound), and
the surface swept by the whole family has correspondingly enormous degree.  Steps 2-3 as planned
(eliminate the swept surface, then a degree <= 35 linear test) are not feasible.
What could still work: low-degree components of the parameter curve (special sub-families defined over
a small field), or a different, lower-degree family of curves on T.  Neither is in hand.
