# Odd contact support forces fourth-power divisibility of the actual indexed norm

This is a separate extension to the fixed-h slot190 appendix. It
does not alter the already reviewed known16 files. It strengthens
the necessary contact condition and eliminates a concrete candidate
with two new genuine shallow coefficient primes. It finds no point.

## Exact local obstruction, without assuming coefficient integrality

Fix h≠0,1, admissible nonzero labels, and the four nonzero rational
guards. Let w be the same literal DetectorGateWitness and use one
of its actual fixed nonzero scales c. Assume a prime p≠2,3,7,17,
c and Δ=c²t−1 are p-units, and the literal contact F(c²t)
has odd valuation e>0. Let d=v_p(w37), finite since
w37=Norm(chartU(h))≠0 at the retained guard.

The three weights seen by the original fold then have valuations
−e,−7e,−25e, all odd. At *every* extension of v_p to Q(√2),
the sixteen original coefficients have even valuation or vanish.
This is the exact pinned ConstructedLeafParity318.all_even:
its input is the original first107 rows, which follow from
DetectorGateWitness318.witness_first107 at those same guards.
It requires that 2 and 11+6√2 be units; 11+6√2 is integral
with norm 49, so both units at the stipulated p. This lemma is
about any additive valuation on the quadratic field, not just
the selected split embedding or the old prime-pattern output.

The first scalar coefficient is w37² and its weight is w156.
If d≤3e, the exact first post-leaf value X₁=1+w37²w156 at
either embedding has valuation 2d−7e≤−e, since the nonconstant
term has lower valuation than 1. Every subsequent fold step
adds a square of its previous value to a leaf whose valuation
is odd or infinite. An even and an odd finite valuation cannot
cancel, and a zero leaf changes nothing. This is also the
literal valuation rule ValuationEvenNormChain.step_value.
Therefore inductively at each embedding the final X satisfies

    v(X) ≤ 2^15 (2d−7e) ≤ −2^15 e.

The same conclusion applies to the conjugate. At inert p this
can be read in the unramified quadratic completion (or by
conjugating the normalized valuation on Q(√2)); no split root
is needed for this estimate. In either case the rational sum

    1/X + 1/X̄ = 2 Re(X)/Norm(X)

has valuation at least 2^15 e. If its value is zero, the
literal total-divide trace gives b=0, already excluded for
a genuine nonzero prepared pole. Otherwise the actual pole
b=(Norm(X)/(2 Re(X)))² F(c²t)/(c^10 Δ^6) therefore satisfies

    v_p(b) ≤ (1−2^16)e < 0,   v_p(b) ≡ e (mod 2).

This is a negative odd valuation, forbidden by a literal
PointPair at p≠3,17 (dd5d6ca1…). Thus any such odd contact
must satisfy **v_p(w37)≥3e+1**, in particular at least four.
This conclusion does not require the remaining coefficient
coordinates to be integral or computed at p. It is necessary
only; reaching that depth need not be sufficient.

For the unscaled slot190 a sharper finite exceptional set is
therefore available. Outside primes dividing

    2·3·5·7·17·2399·407·2398·439,

any odd contact-numerator contribution to a viable t must come
from a prime p with p⁴ dividing the reduced numerator of
the **one actual w37**. The fixed constants cover the exact
contact denominators and determinants and numerator of F(1).
At a good odd numerator factor T=t must then be integral,
Δ is a unit, and its v(F)>0 equals that of the unique
vanishing numerator factor, as in the preceding genus-five
and known16 proofs. No factorization of w37 or the full
fourth-power support is supplied. This refinement removes
the need to treat the other 32 coefficient denominators as
exceptional primes for this necessity. For a scaled pole,
also exclude primes at which the fixed scale is not a unit.

## A concrete necessary-symbol tuple eliminated on the actual h

Keep the exact retuned h in the checked prefix JSON 5a70adc6….
The original G_i signs do permit the nominated tuple
(γ₁,γ₂,γ₃,γ₄)=(2,313·577·1489,2399,407) on the square-t
contact chart if one only performs the known root/unit-symbol
checks, with 5,11,37,2399 saturated. The exact replay verifies
the 24/17 and 5 signs and all four signs at the forced square
root T=−1 at each of 313,577,1489. It does not assert that a
rational t realizes these symbols.

The two new primes 313,577 and the old 1489 are all genuine
coefficient exceptions under an unrefined unit test. The exact
two split reductions at each prime show [h]R is formal, and
the checked actual chart U([h]R) modulo p² has valuation
exactly one in *both* arms:

| p | two orders of the original R | U([h]R) mod p² in root order |
|---|---|---|
| 313 | (6,17) | (17528,31926) |
| 577 | (12,145) | (227338,11540) |
| 1489 | (356,778) | (22335,268020) |

Thus d=v_p(w37)=2 at all three. The candidate would require
odd positive e at these literal contact factors and is
impossible by the sharper depth test. The independent exact
finite row replay also gives depth two at 239,769,1657,2039.
These checks are not broader prime scans, do not evaluate
the enormous fixed coefficient vector, and do not address
primes that might genuinely reach depth at least four.

Reproduce with the pinned sibling scalar JSON:

```sh
python3 -B check_actual_shallow_formal.py | cmp - EXACT-SPLIT-SHALLOW-FORMAL-ROWS.json
sha256sum -c SHA256SUMS
```

Pinned formal source inputs (SHA-256 prefixes, unchanged):
ConstructedLeafParity318 31eb4290, ActualDetectorFold318
1bb3b85f, ValuationEvenNormChain 1e551e5e. The local curve
arithmetic in the replay is affine or formal modulo p², with
linear formal addition and translation, so no nonunit denominator
has been inverted. This is a paper consequence and arithmetic
control, not a new Lean-checked theorem.
