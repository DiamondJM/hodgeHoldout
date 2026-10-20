# Seed searches for cover-and-conic constructions

- `sources.py`, `scan_cover.py`: quotient source / deck exponent for every holdout target, and the scan of
  all open instances for the Fermat-cover symmetry (only `one-reflection-y2-sector` has it).
- `seed_family.py`, `seed_num.py`, `seed_or.py`: fqlx's conic family lies on H(alpha_c, beta_c) for every
  parameter r; the beta = alpha members are the roots of the degree-8 polynomial g used for
  `one-reflection-y2-sector` (real root in (-13,-12); all auxiliary quantities sign-definite there).
- `sys.py`, `sys8.py`, `conic_struct.py`: attempts at a conic seed for `holdout-ternary-deformation`.
  The anchored incidence system (12 unknowns) and its 8-unknown reduction did not finish in msolve within
  20-25 minutes, over Q or modulo 65521 (F4 reached degree 14 with 77k x 199k matrices), and the structured
  ansatz of fqlx's shape (X0 = s^2, X2 = t^2, Fermat point free) also did not finish within 15 minutes.
  A usable seed for that instance needs a structured family, not brute force.
