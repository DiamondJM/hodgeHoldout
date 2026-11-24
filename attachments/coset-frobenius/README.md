# Frobenius on the sigma-odd part of H^3(T), T: u^3 + H = 0 (four-plus-two-residual)

Prepared with Claude Code assistance on behalf of DiamondJM.  p-adic numerics; not certified.

Contents
- `coset.patch`      patch for `dr.h` of ToricControlledReduction (Edgar Costa; commit 74cda9e): restriction of
                     the lattice points to one coset of a sublattice (one character of a diagonal group).
- `coset_frob.cpp`   driver (goes into `examples/`).  Both files are derived from LGPL 2.1 code.
- `make_input.py`    input line for T (torus coordinates b, c, d, u; polytope b + c + d + 2u <= 6).
- `run_coset.sh`     runs the two sigma-odd deck pieces at one prime.
- `data/`            outputs: `c{r}_p{p}_N2.txt` (pole-3 columns mod p^2), `c{r}_p{p}_N3.txt` (all columns mod p^3).
- `coset_analyze.py` slope-1 polynomials mod p, factor degrees, trace checks (python-flint).
- `pointcount.py`    independent traces by point counting.
- `lattice_check.py` the invariant ring and the cosets are generated in degree 1.
- `validate/`        two curves on which the pieces are compared with the unpatched program.

Build
    clone ToricControlledReduction and check out commit 74cda9e
    git apply coset.patch && cp coset_frob.cpp examples/
    ./configure && make build/examples/coset_frob.exe build/examples/readfile.exe
    python3 validate/validate.py <path to the clone>
    ./run_coset.sh <path to the clone> 67 0,0,2,0 N2
    python3 coset_analyze.py
