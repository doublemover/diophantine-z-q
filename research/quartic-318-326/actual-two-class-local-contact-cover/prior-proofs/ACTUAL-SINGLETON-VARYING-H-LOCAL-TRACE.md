# One actual retuned split prime in the original unscaled detector

This is a positive **one-place** retune on the original a=0 source,
not a full contact factor pattern or a rational PointPair. Keep the
exact J and all four literal labels of 5a70adc6 and a7dd144b, and vary h.
At p=3162001 there is an actual contact parameter class and index h
that give v_p(b_190)=1, using all sixteen original fold leaves.

## Exact input, index and contact local row

The prime 3162001=1065²+1424² satisfies the original Gaussian norm
residues (A,B)=(9,0) mod16, (1,3) mod7, and p=1 mod408.
The independent test needed here is the actual residue order of the
original half-point R, not a guess from that ray:

| arm | sqrt(2) mod p | order of R | first-return formal z mod p² |
| --- | ---: | ---: | ---: |
| opposite | 772448 | 791033=29·27277 | 6835326019709 |
| primary | 2389553 | 98746=2·97·509 | 1023381623650 |

Prime factors, both lifted roots, exact order and proper quotient
tests are recorded by the checker. Both last entries are zero
mod p and nonzero mod p², hence depth one.

Let H_old be the 261-bit retained h in 5a70adc6, and L0 its literal
h_CRT_step. In addition to the old exact h congruence modulo L0,
preserve the compact scalar at precision two at 53,131,1041427.
At these three inert places the exact residue orders are 340,44,347142.
In each place [H_old/q]R is formal of exact depth one, independently
checked mod q². Thus the original U_h has exact depth two at each.
Set

    L = lcm(L0, 53³·340, 131³·44, 1041427³·347142).

The literal label index i=6^15·3^65536 J stays fixed, including in
the quotient; it is an integer multiple of H_old. Translating
H_old by a multiple of L leaves its U chart unchanged mod q^4
in the formal disk. Dividing by U_h therefore preserves U_i/U_h
mod q² (U_i has valuation at least two, both U_h values exactly
two); this quotient flows into W through its fourth norm power.
The N term is also preserved. At these primes the remaining
rational constants R and 1+A are units. Away from these three,
the old regular scalar residues at 6551,2470991,16782959 are
preserved by L0, which is divisible by their certified p² periods.
This preserves those *finite scalar rows*, not the exact scalar
b or its full squarefree support.

The positive modulus L has gcd 2 with the primary order and gcd 1
with the opposite order, and p divides none of L or the two orders.
They are relatively prime to one another and H_old is even. Hence
the exact generalized CRT gives

    h = H_old mod L,
    h = 0 mod 98746,
    h = 1 mod 791033,
    h = p³ mod p⁴.

The new h and progression modulus are recorded in the JSON.
The least nonnegative residue itself is positive and exceeds 1.
The directed-rounding chart computation certifies its actual
N(U_h) in
[1534847116899807008,1534847116899807018]/2^64,
strictly past the original 1/100 requirement.
It is still zero mod 5, giving the same four nonzero rational guard
residues (4,1,1,1), with the same n_j labels. In particular there is no
unverified change of real center or inference from just the CRT.

For the literal unscaled detector c=1, choose a square contact
t=(r/d)^2 with d=204 and r=767389608247987 as a first exact test.
The five homogeneous contact numerators (including G0=r²) have
the mod-p² values in the JSON; only G2=r²+d² vanishes mod p,
and it does not vanish mod p². Delta=t−1 and d are p-units.
More generally choose d supported at 2,3,17 with any required
depths and take r congruent modulo p² to d times the certified
root of p−1 mod p²; this imposes t≡−1+p mod p².
Impose also r≡1 mod 2·3·17. Increasing r on that progression
makes t arbitrarily large and does not change the local test.
The displayed d is a local example, not a certified triple
small-place readiness threshold for all scaled detectors.

## Actual local sixteen-leaf consequence

Take Pi=p, Mminus=98746, Mplus=791033. The CRT ensures the original
strong formal orders, primary congruence mod Pi³Mminus and opposite
residue 1 mod Mplus. This uses the *full* original half-point formal
group at both places, not the weaker necessary early-eight modulus.
At the exact chosen h the primary depth of w37 is 1+3=4; the
opposite contributes zero by the signed depth identity (p≠41).

For clarity, the one-place trace proof does not invoke an all-prime
Values family around this singleton. Its pointwise source lemmas are:

1. SelectedActualChartLeaves318.depths from the exact full order
   formal entries supplies the eight source chart bounds.
2. ActualAlternateRatioPrecision318.selected at these same residues
   supplies primary precision 16 and alternate precision 8/16.
   ActualSixComparisonValues318.comparisons uses the actual beta
   and Lucas label equalities for the six polynomial/Padé bounds.
3. SelectedNormTestValues318.norm_tests gives the other two tests
   at the same h, since p>76176; together they give
   ConstructedPrimaryDepths318.Remaining.
4. Because v_p(F(t))=1 and Delta,c are units, the literal weights
   have values −1,−7,−25. ConstructedPrimaryDepths318.all_positive
   applies to the exact first107 assignment at its four nonzero
   rational guards and proves positivity of all weighted leaves
   on the primary arm. ConstructedLeafParity318.all_even gives the
   opposite even-or-zero coefficients; the same weights are odd.
5. ActualDetectorTrace318.scaled_trace_unit yields a unit trace
   quotient. The literal unscaled pole equation therefore has
   v_p(b_190)=1 and nonzero real-chain denominator at this p.

All of these are instantiations of pointwise arithmetic within
the source; the stronger wrapped selected prime family is not
invoked and no new Lean declaration is claimed.

## Scope and replay

The retune constructs one specific h and maintains one chosen
positive-depth good odd prime in the exact unscaled slot. It says
nothing about other odd prime divisors of the same contact value
or those from the other two scales. It is not a complete square
denominator result, a prime pattern, result on all four linked
poles, or any rational realization.

    python3 -B check_actual_singleton_retune.py | cmp - EXACT-SINGLETON-RETUNE.json
    sha256sum -c SHA256SUMS

The checker uses exact pinned sibling arithmetic sources and
only checks the listed primes; no broad scan is a replay input.
