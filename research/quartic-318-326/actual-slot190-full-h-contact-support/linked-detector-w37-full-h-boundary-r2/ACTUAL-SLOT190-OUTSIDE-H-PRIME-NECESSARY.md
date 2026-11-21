# The fixed slot190 now requires a prime outside the entire h-support

Version r2 supersedes the r1 widened-mask check: the old free-5
squareclass restriction cannot be inherited after adding six primes.
The factorization and local depth calculations are unchanged; the
conclusion below now uses all four possible 5-adic branches.

Same exact fixed h, same original unscaled slot190, and same square-contact
chart as the reviewed known16 appendix. Let t=(R/D)^2>2, with reduced
positive denominator D, v_2(D)>=2, and 3 and 17 dividing D. Let the
retained pole be defined and nonzero. We prove that if this pole has a
literal PointPair, then one of its odd positive contact numerator
valuations occurs at a prime **outside both the known16 universe and
the complete prime support of h**. The alternative rank-zero tuple is
also excluded, exactly as in known16.

For that required outside prime the signed depth proof 8f4cc314 implies
that the original elliptic generator is genuinely Wieferich at a
specified arm: its first return to the identity modulo the prime also
returns modulo the square of that prime. The stronger depth conditions
in that proof apply if the arm is split. We do not supply such a prime,
rule all such primes out, claim a non-square-contact result, or claim a
PointPair.

## 1. Exact integer and primality certificates

The integer retained in source 5a70adc6 has the exact factorization

    h = 2^6 · 3^8 · 5 · 11 · 13 · 17 · 29 · 31 · 41 · 47 · 53
        · 73 · 89 · 131 · 337 · 389 · 1231 · 4261 · 1041427
        · 472879111 · 26773696669 · 739721042333238923.

The script multiplies these factors and compares with the literal donor h.
For each factor above 5000, a recursive full factorization of p-1 and
a Fermat witness a have

    a^(p-1) = 1 mod p,
    gcd(a^((p-1)/q)-1,p) = 1 for every prime q dividing p-1.

These equalities are checked by exact integer arithmetic. For any prime
l|p they force the order of a modulo l to be p-1, giving l>=p. Smaller
certificate factors are trial-divided up to their integer square roots.
Thus no unproved probable-prime or factorization claim enters the output.
The arithmetic replay does not require the method that found the factors.

## 2. All local support at h

The fixed exception integer from the threshold proof is
2·3·5·7·17·2399·407·2398·439. Of the h factors it removes exactly
2,3,5,11,17; all either already handled in known16 or excluded by the
stated D conditions. At each remaining h-prime calculate the reductions
of the literal Q=[2h]R from the depth theorem, at each actual arm.
At a positive arm compute the formal parameter of [2h/p]R modulo p^2:
here every nonfixed h-prime has exponent one, and the computation checks
that this divided index is still formal. Its first nonzero formal depth
increases by exactly one on applying [p] (A in 8f4cc314). If the divided
index is already zero modulo p^2, retain only the lower bound. If Q is
affine with nonzero x modulo p, its depth contribution is zero; the
checker explicitly rejects accidentally treating the T0 pole as zero.
At inert primes double the one arm's normalized contribution.

Write G_1=2u+v, G_2=u+v, G_3=2399u-v, G_4=407u+32v
for the four moving forms on primitive contact (u,v)=(R^2,D^2).
For every p in this table the leading and constant coefficients are
units, so a p dividing one of these forms must have D unit and T=u/v
a square root-chart value with T=-b_i/a_i; equivalently
(-a_i b_i/p)=+1. The same h-prime data are:

| p | exact norm depth or guaranteed interval | eligible form numbers |
| ---: | ---: | --- |
| 13 | 4 | 2 |
| 29 | 4 | 2 |
| 31 | 4 | none |
| 41 | 4 | 1,2,3 |
| 47 | at least 5 | 3,4 |
| 53 | 4 | 2 |
| 73 | 4 | 1,2 |
| 89 | 2 | 1,2,3 |
| 131 | 4 | 1,3 |
| 337 | 4 | 1,2 |
| 389 | 4 | 2,3,4 |
| 1231 | 0 | none |
| 4261 | 0 | 2,4 |
| 1041427 | 4 | 1,3,4 |
| 472879111 | 0 | none |
| 26773696669 | 0 | 2,3,4 |
| 739721042333238923 | 0 | 1 |

There is no need to assert the exact second-arm depth at 47. The only
possibly eligible h-primes outside known16 are 29,41,47,73,337,389.
The filter is deliberately permissive: retaining one does not claim
it occurs in a rational t or suffices for the contact itself.

## 3. Complete finite widened test (not complete global support)

Enlarge the known16 candidate universe by exactly these six primes.
Their pairwise-form determinants are still units at all ordinary
universe primes (checked against every pair of forms). Thus outside 5
the same square-root gates, all ordinary saturation relaxations and
the eight possibilities at 11,37,2399 are valid. At 7 there still
is no square T root. **The old free-5 gate T=1 is not valid after
enlarging the universe.** A new product can now make G1's squareclass
square modulo 5, so the exact 5-adic chart is rebuilt independently.

For a positive squarefree Gamma_i with G_i=Gamma_i times a square,
record its local tag (epsilon_i, chi_i), where epsilon_i is the
parity valuation at 5 and chi_i is the Legendre symbol of its
normalized 5-unit. If 5 divides D the tags are those of the leading
coefficients (the remaining R^2 is a unit square). Otherwise the
square T=R^2/D^2 has residue 0,1, or 4; the common unit square D^2
does not affect the tags. T=0 gives (+,+,+,-) and T=1 gives
(-,-,-,+), with all valuation bits zero. At T=4 put T=-1+5x.
The nonunit forms are exactly

    G2(T,1)=5x,
    G3(T,1)=5(2399x-480),
    G4(T,1)=5(407x-75).

Enumerating x mod 125 determines all tags except possibly one at
a residue where its form vanishes modulo 625: no two can vanish
to depth four because their pairwise determinants have at most
5-adic depth three. For that single one allow all four tags: after
writing x=x0+125y, its quotient by 625 is affine in y with
5-unit slope, so both signs at both valuation parities occur.
All possible T=-1+5x are local squares, and an exact zero of a
form is excluded by the actual contact premise. This is a finite
exhaustive 16-tag branch at T=4, distinct from the three single-tag
branches.

The finite widened checker assigns 5 parity separately to each form,
and uses its normalized unit symbol at 5, but the full squareclass
(including the 5 factor) in all 24/17 and cross-symbol tests. All
32 bins of the form (one of eight non-5 masks, one of the four
5-adic branches) are checked. Thirty-one give no tuple. In the one
fully saturated case the only tuple is (2,1,2399,407), killed by
the same area-2 / torsion-only E_2 argument from the reviewed
appendix. An independent verifier also allows a strictly larger
set of possible T=4 tags (independent parity bits on G2,G3,G4 and
no corresponding unit constraint), reaching precisely the same
sole tuple. This exhaustion is of the proposed larger finite
support, not of unknown primes in general.

All fixed contact exceptions not excluded by the D conditions are
already included in known16. Thus, for a putative literal PointPair in
the stated chart, some odd positive numerator exponent necessarily
comes from a prime p outside known16 and outside the entire support of
h. Since t is a square, the extra contact factor G_0=u is square and
cannot account for an odd numerator exponent. At the newly necessary
prime the scale and Delta are units, its parity is that of the unique
form having a root, and 8a0f698e requires v_p(w37)>=3e+1.
Then 8f4cc314 gives the actual first-appearance elliptic depth
requirement stated above. This isolates a genuine outside-h
Wieferich issue instead of leaving ordinary h-factor divisibility as
an untested possibility.

## Replay

The script pins and consumes exactly these author sibling sources:
linked-detector-known16-exhaustion-r1/check_fixed_h_known16.py
and linked-detector-w37-depth-r1/check_actual_shallow_formal.py.
Their two exact input JSON donors remain their original path relatives.
The forwarded mod-p^2 group law is the already audited one.
The old leading-prime and cross-determinant data are reused; the
widened support and exact 5-adic branches are evaluated afresh.

    sha256sum -c SHA256SUMS
    python3 -B check_actual_h_prime_boundary.py | cmp - EXACT-ALL-H-PRIME-BOUNDARY.json

No Lean compilation, unrelated prime scan, or materialization of the
large elliptic point is involved.
