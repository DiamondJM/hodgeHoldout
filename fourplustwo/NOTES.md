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

## Thread state on 2026-11-24 (discussion 120, read through the `thread`/`read` workflow actions)
The four-variable core equation is now the common formulation on the thread.
 * kmehltretter82 (11-16, 11-21): Lean formalisation of the core reduction, Euler gauge and suspension;
   for any D with H not dividing D, a core certificate is equivalent to the strict system
       p(H) = A D,   D div p = p(D).
   Degree-6 diagnostics: admissible D form a 49-dim space W = {D : A D in J(H)} (28 + 21 by parity), the
   Koszul freedom is 60-dimensional, and projecting to (R_H)_12 gives 35 independent quadrics on P^48.
 * benediamond (11-17): any degree-6 denominator is D_c(x) + lambda F with [D_c] nonzero in a 33-dim subspace
   of (R_H)_6; a degree-6 certificate exists iff the strict system has a solution with D sextic.  Open.
 * Robertboy18 (11-23): could not finish degree 6.  A degree-6 denominator would put the class alpha_A into a
   proper deck-stable sub-Hodge structure of H^3(T)^- (his bounds 44 and 36 < 48, unreviewed); several shapes
   of D excluded; direct elimination sized at a 396704 x 350658 Macaulay matrix, not run.  He asks for the
   full characteristic polynomial of Frobenius on that eigenspace at one prime, to test simplicity.
 * benediamond (11-06, before our note): an explicit contact family on this core whose cylinder map spans the
   anti-invariant cohomology; our numerical norm-contact model overlapped with it.

Possible contribution: the Frobenius characteristic polynomial on H^3(T)^- (degree 96 over Q, two conjugate
degree-48 factors over Q(zeta_3) for p = 1 mod 3; p = 7 is bad because of the 5/7 coefficients).  Point counting
cannot reach degree 48.  The published p-adic method (Costa-Harvey-Kedlaya, ToricControlledReduction) handles
degree-6 hypersurfaces in P(1,1,1,1,2); it was cloned but NOT built or run (building third-party code needs
the user's approval in this environment).

## Frobenius computation: status on 2026-11-24 (frobenius/)
Software: edgarcosta/ToricControlledReduction (GPL), built from source with the user's approval; it reproduces
its shipped examples and the Dwork quintic through the file interface (`readfile.exe`).
Input: T: u^3 + H = 0 in P(1,1,1,1,2), chart a = 1, torus coordinates (b,c,d,u), polytope
{w >= 0, b+c+d+2u <= 6} (`make_input.py`).
 * p = 13: rejected as degenerate; 13 divides disc h_Y (disc h_X = 3^2 * 29 * 23401711321,
   disc h_Y = 2^2 * 13 * 1277 * 7237 * 189547).
 * p = 19: passes that check, then stops: the implementation needs p >= 2(weight+1) + max r = 62.
 * p = 67 (smallest usable prime; 67 = 1 mod 6): killed by the kernel at 14 GB (container limit 15 GB).
   The top-level dense solve matrix alone is 5*|4P| x |5P| = 55055 x 24616, about 10.8 GB.
Independent point counts (`pointcount.py`): Tr(Frob | H^3(T)) = 97, 207, -812, 376 at p = 13, 19, 31, 67, and on
the sigma-odd part 78, 133, -155, 134.  These are the check values for any Frobenius computation.
Way to make it fit: the exponents of f generate the sublattice M' = {u = 0 mod 3, c+d even} of index 6, so the
graded module splits into 6 cosets = characters of (deck, sigma), preserved by Frobenius when p = 1 mod 6.
The (sigma-odd, omega) coset has 16, 156, 636, 1780, 4020 points in kP for k = 1..5 (130, 1036, 4015, 11011,
24616 in total), so its top-level matrix is about 0.3 GB.  The library has no such restriction; it would have
to be patched (module points in the coset, reduction directions in M'), or run unmodified on a machine with
several times more memory.
