#!/bin/bash
# Frobenius on the two sigma-odd deck pieces of H^3(T) at one prime, with the patched library.
#   usage: run_coset.sh <dir of the patched ToricControlledReduction build> <p> <N_1,N_2,N_3,N_4> <tag>
# e.g.   run_coset.sh ~/ToricControlledReduction 67 0,0,2,0 N2     (pole-3 columns mod p^2)
#        run_coset.sh ~/ToricControlledReduction 19 0,3,3,0 N3     (all columns mod p^3)
# Build: clone edgarcosta/ToricControlledReduction (commit 74cda9e), `git apply coset.patch`,
# copy coset_frob.cpp to examples/, then ./configure && make build/examples/coset_frob.exe
set -e
here="$(cd "$(dirname "$0")" && pwd)"
B="$1/build/examples"; p=$2; N=$3; tag=$4
mkdir -p "$here/data"
python3 "$here/make_input.py" $p > "$here/data/in$p.txt"
for r in 1 2; do
  # exponents (b,c,d,u): c + d odd (sigma-odd), u = r mod 3 (deck character)
  "$B/coset_frob.exe" "$here/data/in$p.txt" "$here/data/c${r}_p${p}_${tag}.txt" "0 1 1 0 2 1; 0 0 0 1 3 $r" $N
done
