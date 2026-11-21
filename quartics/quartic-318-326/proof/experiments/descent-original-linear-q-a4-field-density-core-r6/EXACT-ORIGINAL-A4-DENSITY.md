# Actual linear-q numerator masks: exact local density

The same squarefree A4 sieve density `ActualA4LinearNormForms318.localBad`
has the following exact odd-good-prime cardinal, not just a union bound.
Write (r) for the number of merged norm sites including q, (p) for
the modulus, (chi=chi_4(p)), (A=p+(p-1)chi), and
(B=p^3+p^2-p). Then
[
#mathrm{localBad}_p=2Ap^2+(r-2)B-(r-1)A^2 .
]
After division by (p^4) the error from ((r+2chi)/p) is at most
(6r/p^2). The two observed sites contribute (Ap^2) each even when
one is q. Off the two-norm-zero common core all r masks are disjoint:
an invertible pair of projective coefficient rows forces both norms
to be zero, exactly. Thus the correction is ((r-1)A^2), not a
generic higher-overlap or Bonferroni error. This is the same local
mask in the 14-module finite-sieve upper, not a new sampling law.

The nonvanishing hypotheses specify exactly which finite primes
must be excluded. The integer numerator determinant times the
observed determinant equals the product of its two literal
denominators times the original two-form determinant; the latter
is (pm 1) if one site is q and a nonzero slope difference
times (Q^2) otherwise. All denominators/minors are fixed before
the free prime cutoff. `ActualA4ProjectiveCoefficients318.axes`
proves the two distinct observed coefficient axes have the opposite
coefficient zero. Nonzero determinants give nonzero remaining
coefficients for every other site. No angular prime condition enters
the upper bound.

`ActualA4FieldNormCount318` splices the exact same finite conic,
norm, and norm-difference calculations of `FiniteDifferenceConic318`,
`FiniteGaussianNormCount318`, and `FiniteNormDifferenceCount318`
from pinned RC-selected source; the one directly imported Mathlib
quadratic-character square-fibre calculation eliminates unrelated
index-selection dependencies. No claim of inherited hosted status
through this relocation. (chi=chi_4(p)) follows using the ordinary
odd-prime -1 square test; the native statement retains the precise
`quadraticChar (ZMod p) (-1)` needed by that character map.

These uncompiled source modules supply the mathematically exact local
denominator data (same finite mask). They do not assert a Selberg
minimizer, logarithmic denominator lower, Mertens, or physical large
tail. Test `control_density.py` enumerates only small finite-field
cells (no search for original keys).
