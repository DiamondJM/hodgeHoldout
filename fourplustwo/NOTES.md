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
Software: edgarcosta/ToricControlledReduction (LGPL 2.1), built from source with the user's approval; it reproduces
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

## Frobenius on H^3(T)^-: coset patch and result (2026-11-24, frobenius/)
Patch (`coset.patch` against commit 74cda9e of ToricControlledReduction, plus the driver `coset_frob.cpp`;
both derived from LGPL code).  A `dr` object can be restricted to the lattice points in one coset of
M' = {c+d even, u = 0 mod 3}.  Two objects are used: the invariant ring (trivial coset) supplies every
Jacobian relation and every reduction matrix; the coset module supplies the basis, pi/rho and the last
reduction.  Frobenius of a coset monomial is reduced along directions of the invariant ring only, so every
intermediate monomial stays in the coset.  The last step (pole p -> pole 1 at a coset point u of P) cannot use
the direction u itself; it uses 6u = sum of six ring points of P and (p-1)/6 steps for each.  Needs p = 1 mod 6.
`lattice_check.py`: the ring and all five nontrivial cosets are generated in degree 1 (so directions exist).

Sizes for the piece (c+d odd, u = 1 mod 3): dim J' = (1,40,61,6) for the ring, (0,16,76,16) for the module;
initialisation one minute, 16 Frobenius columns at N = 2 in ten seconds.

Validation.
 * `validate/validate.py`: on y^2 = sextic in x^2 (involution) and on a Picard curve (order 3, asymmetric Hodge
   numbers) over F_13, the product of the pieces' characteristic polynomials equals the stock program's zeta
   polynomial mod 13^3 resp. 13^4.
 * On T: the trace on the 96-dimensional sigma-odd part, summed over the two deck pieces, equals the point count
   of `pointcount.py`: 133 mod 19^3, -155 mod 31^3 and 134 mod 67^3 (runs N3: all columns mod p^3).
 * All entries outside H^3(T) (the complement classes) vanish; pole-m columns are divisible by p^(4-m).

Result (`coset_analyze.py`, data in `data/`).  Hodge numbers (h30,h21,h12,h03): piece 1 (u = 1 mod 3) is
(0,32,16,0), piece 2 is (0,16,32,0); the pieces are dual.  At p = 19, 31, 37, 43, 61, 67, 73, 79, 103, 109,
127, 139 (all p = 1 mod 6 below 140 except 7, which divides the denominators of H, and 13 and 97, which the
program rejects as degenerate) Frobenius is
ordinary: on piece 1 slopes 1 (x16) and 2 (x32).  Degrees of the irreducible factors over Q_p:

    p     slope 1 (16)        slope 2 (32)
    19    1,1,7,7             6,9,17
    31    1,15                (not squarefree mod p)
    37    16                  1,6,25
    43    1,1,2,3,9           1,1,5,6,7,12
    61    1,2,13              1,6,25
    67    1,6,9               2,3,27
    73    2,3,11              1,3,5,23
    79    1,2,6,7             1,2,4,12,13
    103   2,4,10              1,3,12,16
    109   1,6,9               12,20
    127   7,9                 1,6,25
    139   2,5,9               1,2,11,18

Consequence.  Let W be a deck-stable sub-object of H^3(T)^- on which Frobenius has characteristic polynomial
in Q(omega)[T] at each of these primes and which has Hodge numbers (so: a motivic sub-Hodge structure).  Its
slope-1 rank is h12 of its piece-1 part and its slope-2 rank is h21, the same at every ordinary prime.
p = 37 forces the slope-1 rank into {0,16}; p = 19, 37, 67 (also 109, 127) force the slope-2 rank into {0,32}.
Mixed cases (16,0) and (0,32): all eigenvalues would have valuations (1,2) resp. (2,1) at the two primes above
p, hence be pi*pibar^2 resp. pi^2*pibar times roots of unity (Kronecker), with at most 16 resp. 32 conjugates
over Q(omega).  At p = 19 the slope-1 part has factors of degree 7 and the slope-2 part one of degree 17; a
root of unity of degree 7 (17) over Q_19 has at least 28 (102) conjugates over Q(omega).  So W = 0 or all:
H^3(T)^- is simple as a Q(omega)-motive, conditional on these (uncertified) numerics.
Using only the total rank (no Hodge type) the twelve primes leave ranks 1, 6, 7, 16 and their complements.

Second independent check.  kmehltretter82 posted eigen-traces a + b*zeta on V_zeta (thread 120, 2026-11-21):
76+19z, -93-31z, -296-185z, 215+215z, -61-122z at p = 19, 31, 37, 43, 61.  Evaluated at the two cube roots of
unity in Z_p they equal the traces of our two pieces: mod p^3 at p = 19, 31, 37 and mod p^2 at 43, 61.

Number fields (`coset_analyze.py`, function `powers`).  A sub-Hodge structure of geometric origin is defined
over some number field K, so it is only stable under Frob^f at a prime of residue degree f.  The Q_p-factor
degrees of the characteristic polynomial of Frob^f are those of Frob unless sigma^k(alpha)/alpha is a root of
unity for two distinct conjugate roots.  Write a unit root as alpha = teich * (1 + p*eps); then
alpha^(p^d - 1) = 1 - p*eps mod p^2 and the ratio can only be a root of unity if eps mod p lies in a proper
subfield of F_{p^d}.  From the runs N3 (Frob/p mod p^2, unit-root factors by one Hensel step) eps mod p
generates F_{p^d} for every factor at p = 19, 37, 67 (both pieces), the primes used in the argument above; the
detector does flag the control Phi_7(T/3).  Hence the argument holds for every power of Frobenius, and the
conclusion is: no proper nonzero deck-stable sub-Hodge structure of geometric origin over any number field.
The sub-structure in Robertboy18's degree-six argument comes from H^1 of a resolved surface, so it is of
geometric origin; degree six is then excluded provided his bounds 44 and 36 hold (not checked here).

Not done: the exact characteristic polynomial.  Recovering the coefficients in Z[omega] needs about ten
digits of relative precision in both pieces (Newton-identity bounds: r1 + r2 > 16 + small for every k >= 16),
i.e. N about 12; the cost grows like N^5 and the working modulus leaves one machine word.  Out of reach in this
container; the unit-root data above is what relative precision 1 gives.

