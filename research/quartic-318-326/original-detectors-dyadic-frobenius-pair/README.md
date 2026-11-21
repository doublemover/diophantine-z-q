# Two original dyadic Heegner bits as one finite Frobenius condition

Read [the exact proof](source/dyadic/heegner-compressed-trace/original-detectors-dyadic-frobenius-pair-r1/PAIRED-ORIGINAL-DYADIC-BITS-ARE-A-FINITE-FROBENIUS-CONDITION.md)
and the [signed independent review](independent-review/INDEPENDENT-PAIRED-DYADIC-FROBENIUS-REVIEW.md).
Run 'sh verify.sh' for the exact standard-library replays.

Fix one admissible original detector pole, its shared helper choices
and a compatible original residue row for the final shared prime.
The paper constructs a characteristic-zero cusp form whose two
coefficient functionals give the required ordinary dyadic bits for
the two selected twists. A simultaneous 1,1 Frobenius class in that
fixed row would yield infinitely many eligible final primes and the
two required nontorsion Heegner traces. The finite intersection may
be empty. No such class, original bit, trace, point, or rank is
computed. The level and weight are existence bounds, not estimates
for a practical modular-form enumeration.

The exact proof, immediate donor files and independent receipt are
preserved verbatim. Replays check the finite Faber/edge and local
input computations; they do not compute the Hecke algebra or its
Frobenius images.
