# cycle-q2: fixed-denominator solver for the canonical tangent equation

Files for the discussion note "A solver and a low-degree exclusion for the canonical tangent equation of cycle-q2".

- `ct.py`: the solver. `solve(H)` tests one denominator H (free of Y2, semi-invariant under the diagonal
  symmetry group) by linear algebra modulo p. Running `python3 ct.py` prints the group order and two sample tests.
- `relax.py`: exhaustive exclusion by linearisation, one symmetry class at a time.
  `python3 relax.py 9` reproduces degrees 1 to 9 (about twenty minutes on four cores; degree 9 dominates).
- `kernel6.py`: exhibits the spurious degree-6 kernel vector that appears if the product unknowns are
  indexed by pairs instead of by distinct monomial products.

Requirements: Python 3.11+, python-flint 0.9. The prime is 1000003; set the environment variable `CTP` to change it.
All results are modular evidence, not proofs. Prepared with Claude Code assistance for `DiamondJM`.
