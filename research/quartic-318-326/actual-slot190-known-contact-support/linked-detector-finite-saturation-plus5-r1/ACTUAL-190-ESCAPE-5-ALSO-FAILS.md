# The exact fixed-h detector saturation still fails if 5 is also left free

Use the actual symbolic same-index t family and B_bad construction of
a6082bf3… with the **same** retuned h,J, original labels and original
slot190. This version enlarges the fifteen-prime S_free to sixteen by
adding 5, and makes no independent changes to D, R or t except the
declared removal of 5 from the set of saturated primes. Small-prime
and archimedean pre-pole requirements remain, with D always deep at
2,3,17; in particular none of the omitted primes is one of those.
The obstruction uses only the exact first and fourth nonzero contact
numerators, G1=2R²+D² and G4=407R²+32D².

As before, if a literal PointPair exists, outside the fixed exceptional
set every positive G_i exponent is even. On the saturated primes
the valuations are exactly those of the leading coefficients.
For G4, both 11 and 37 are unsaturated; neither divides G4 even
once since 32D² is a unit there. Thus its entire squarefree part
must come from the eligible unsaturated primes, defined by
(−32·407/p)=+1. There is now exactly one eligible p≡2 mod3:
p=5. Since G4 is a 3-unit with residue 2, its positive squarefree
part must contain 5. In particular, modulo 5 the actual equality
G4≡0 forces R²/D²≡−1; both D and R are units.

At all saturated primes only the leading factor 2 contributes to
the squarefree class of G1. Every unsaturated prime that can
contribute to G1/2 satisfies (−2/p)=+1. The eligible subset is
exactly {11,131,163,1489,1041427}, none divisible by 5. Write

    G1 = 2 d X²

with positive d a squarefree product of that set. Because D is
deep at 2,3,17, the unit G1/2=R²+D²/2 is a square at each
of those three places. Therefore d≡1 mod24 and (d/17)=+.
The complete enumeration of 32 possibilities gives

    d ∈ {1, 11·131, 163·1041427, 11·131·163·1041427}.

All four d are 1 mod5, so the factor 2 makes 2d a nonsquare
mod5. But G1/D²≡2(−1)+1=−1 at 5, a nonzero square.
That's an exact contradiction on this fixed h, wholly independent
of the standard four-form determinant compatibility at 5 or
of a rank computation at the putative twist.

Thus allowing 5 alone **does not** rescue this natural construction.
At least one genuinely new free prime or a change in which leading
prime is saturated (e.g. restore 11 to D), or a different t chart,
is needed to escape this proof. None of those conditions alone
is sufficient for a point. We have evaluated no actual detector
curve rank and found no original PointPair or global general
obstruction. This is an exact finite rejection of the specified
same-index prefix family, including arbitrary N past the original
archimedean threshold.

```sh
python3 -B check_contact_two_form_plus5.py | cmp - EXACT-CONTACT-TWO-FORM-PLUS5.json
sha256sum -c SHA256SUMS
```
