# The selected q53 principal row does not reduce to the small factor base

Keep the exact principal norm and the
[complete factor-free mirror ideal relation](../actual-one-I-q53-relative-gaussian-r1/EXACT-FACTOR-FREE-MIRROR-Q53-CLASS-RELATION.md).
There is no factor search over arbitrary candidates:
this is an exact smoothness test of the one fixed
2940-digit complement C of gamma=Z−G(B).

A complete segmented Eratosthenes sieve enumerates all
8,444,396 rational primes at most 150,000,000, and GMP
checks divisibility of exactly C by each. No prime
divides it. The count is independently cross-checked
by primepi, and the residual integer is unchanged.
The segment covers each integer from 2 to the bound
once, marking multiples of primes through the square
root of the segment end, so nothing is inferred from
a search timeout or a truncated prime table.

The exact relative Gaussian polynomial and the
two unit derivative tests earlier prove that all
the supported C-primes have residue degree one
in the mirror and lie in free relative scalar orbits.
Moreover C^4≡24 (mod53) rules out a total 13th power.
Therefore a nonzero projected **divisor** component
survives outside the whole 150-million norm bound.
The ordinary class of that component is not known.

As a consequence, the particular principal relation
for q_53 cannot by itself express the test ideal using
only primes in a factor base below 150 million. This
includes the earlier **conditional GRH** comparison
bound 148,614,287, but the divisibility and divisor
statements here are unconditional. A different relation
or further certified ideal reductions might still
represent the same class with small ideals. No class
nontriviality, general complexity lower bound, class
generation, Selmer dimension, or rational rank is
asserted.

    sha256sum -c SHA256SUMS
    set -o pipefail
    exe=$(mktemp)
    c++ -std=c++17 -O3 check_q53_smoothness.cpp -lgmpxx -lgmp -o "$exe"
    python3 -B exact_q53_cofactor.py | "$exe" 150000000 | cmp - EXACT-Q53-COMPLEMENT-150M-SIEVE.json
    rm -f "$exe"
    python3 -B verify_q53_sieve_output.py
