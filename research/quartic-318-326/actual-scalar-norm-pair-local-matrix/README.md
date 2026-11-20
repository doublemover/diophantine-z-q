# The fixed scalar's alternate next cover and exact local matrix

These notes keep the materialized scalar of the original 318/326
construction unchanged, at the published index
$h=473592745039516333133760$. They give an exact degree-two
cover of the alternate genus-one curve and an if-and-only-if local
test on its normalized covering classes. They also give bounded
prime-support computations and an exact rank check on the known
local rows. They do not decide the full local system on unknown
support or exhibit a rational point.

## Read in this order

1. [The reviewed alternate curve and the original point transport](rc-linked-scalar-norm-pair-r1/ALTERNATE-NORM-PAIR-GENUS-ONE-ROUTE.md).
2. [The exact next cover and the odd-depth tangent test](rc-linked-scalar-norm-pair-next-r1/NEXT-COVER-AND-ACTUAL-ODD-DISCRIMINANT-TEST.md).
3. [All local unit classes at the new discriminant primes](rc-linked-scalar-norm-pair-next-L-class-r1/EXACT-SHARED-BRANCH-LOCAL-CLASSES.md)
   and [the remaining places and complete finite local test](rc-linked-scalar-norm-pair-next-odd-places-r1/EXACT-REMAINING-ODD-PLACES.md).
4. [Actual support checks, formal zero recovery, and the exact local matrix](rc-linked-scalar-norm-pair-support-r1/ACTUAL-ALT-SUPPORT-AND-KNOWN-MATRIX.md).

For the original specialization, earlier support, and denominator
normalization the companion directories contain the exact cited proof
notes and the source data used by the current replay. In particular
the original two scalar Python helpers are byte-identical to those
published in the fixed-scalar snapshot at `e2ef09a`.

[Independent verification receipt](INDEPENDENT-ALTERNATE-LOCAL-AND-KNOWN-SUPPORT.md)
records exactly which parts were independently replayed and which
C++ scans were spot-checked.

The exact 20-million scan covers all relevant primes outside the
fixed places. The 20-to-120-million scan covers only the stricter
rank-dependent locus described in the note. The 11 rows are
independent on 12 known support columns and leave exactly two
lifts for each formal right-hand side. This does not compute
the actual right-hand side or exclude additional rows and columns.
The four fixed denominator factors are known; the exceptional
reduced-denominator characters are not evaluated.

## Source-only replay

From this directory, with Python 3.10+ and a C++17 compiler:

    sha256sum -c SHA256SUMS
    PYTHONDONTWRITEBYTECODE=1 python3 rc-linked-scalar-norm-pair-r1/check_alt_critical_prime.py | cmp - rc-linked-scalar-norm-pair-r1/ACTUAL-ALT-PRIME-83.json
    PYTHONDONTWRITEBYTECODE=1 python3 rc-linked-scalar-norm-pair-next-r1/check_shared_line_83.py | cmp - rc-linked-scalar-norm-pair-next-r1/SHARED-LINE-83.json
    PYTHONDONTWRITEBYTECODE=1 python3 rc-linked-scalar-norm-pair-support-r1/check_alt_known_matrix.py | cmp - rc-linked-scalar-norm-pair-support-r1/ACTUAL-ALT-KNOWN-MATRIX.json
    PYTHONDONTWRITEBYTECODE=1 python3 rc-linked-scalar-norm-pair-support-r1/check_alt_formal_ratio_controls.py | cmp - rc-linked-scalar-norm-pair-support-r1/ALT-FORMAL-RATIO-CONTROLS.json
    g++ -std=c++17 -O3 rc-linked-scalar-norm-pair-support-r1/find_alt_discriminant_primes.cpp -o /tmp/find_alt_support
    /tmp/find_alt_support 2000000 | cmp - rc-linked-scalar-norm-pair-support-r1/SCAN-FORMAL-2M.txt
    /tmp/find_alt_support 20000000 2000001 | cmp - rc-linked-scalar-norm-pair-support-r1/SCAN-FORMAL-20M.txt
    /tmp/find_alt_support 120000000 20000001 dependent | cmp - rc-linked-scalar-norm-pair-support-r1/SCAN-FORMAL-DEPENDENT-120M.txt

The calculations use only exact integer, finite-field, or directed
local arithmetic. No expanded large coordinate, external Python
package, network, or Lean check is needed to replay these files.
They are finite arithmetic evidence, not a kernel-checked global
proof.

The supporting residue data are also replayable separately:

    PYTHONDONTWRITEBYTECODE=1 python3 rc-linked-scalar-higher-descent-r2/check_new_H_prime.py 2470991 16782959 | cmp - rc-linked-scalar-higher-descent-r2/ACTUAL-NEW-H-PRIMES.json
    PYTHONDONTWRITEBYTECODE=1 python3 rc-linked-scalar-higher-descent-r3/check_denominator_barrier_constants.py | cmp - rc-linked-scalar-higher-descent-r3/DENOMINATOR-BARRIER-CONSTANTS.json
    PYTHONDONTWRITEBYTECODE=1 python3 rc-linked-scalar-higher-descent-r4/check_normalizer_primes_without_packages.py | cmp - rc-linked-scalar-higher-descent-r4/EXACT-NORMALIZER-PRIMES.json
