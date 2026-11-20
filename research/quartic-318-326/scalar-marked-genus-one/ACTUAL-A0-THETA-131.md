# An actual a=0 scalar progression with theta ramified at 131

Paper implication on original source bytes at baseline
558a130e12a461d9b380b44510d457f0d3d8a29d. This constructs
an admissible actual scalar progression and actual indices;
it does not evaluate the enormous rational b on one index,
supply its full theta factorization, or supply the simultaneous
prime-pattern input for the three detectors.

## Exact arithmetic

Set a=0 (or −1), R=4376874610839020, A=114444 R =
500907037962860804880, and p=131. Then

    R≡30, A≡72, 1+A≡73 (mod 131),
    (1+A)²−A/17 = 250907860680726875559825159650206985141521
                 ≡ 12183 = 93·131 (mod 131²).

The last nonzero unit is literal. The source's scalar identity
is b=A[W/(1+A)]². At any actual index with W≡1 mod131²
in Z_131 it follows that

    v_131(1−b/17)=1,  ((1−b/17)/131)≡82 (mod 131).

Indeed subtract the constant numerator: the difference
is −(A/17)(W²−1) in 131² Z_131, while the denominator
(1+A)² is a unit. The residue 82 is a nonsquare modulo
131. Hence the same extracted theta includes 131
and theta/131 is a nonsquare unit modulo 131. Theta
cannot be 1. This calculation does not assert W=1.

## Why the exact actual scalar supplier meets the congruence

This is a strengthening of the finite-centre proof, not
a new analytic prime-pattern premise, and does not claim
the original arbitrary existential already chose these
representatives. Follow `FiniteScalarCenter318.center_units`
with the actual finite support of A plus the one additional
prime 131, and strengthen only the requested depths there.

1. The actual h_base is chosen first, simultaneously divisible
   by 64 and the old requested M_base. For each support prime
   use the same depth as in `FiniteScalarCenter318.center`.
   At 131 use `GeneralScalarDepth318.scalar_leaves` with r=1,
   which gives depth at least 2 for both
   H=normCoefficient(chartU h_base) and
   2f=2 Re((chartU h_base)²) on every nonzero multiple of
   its positive modulus. Take the product of the finitely many
   moduli, times 64*M_base, exactly as in the original construction.
   The actual nonzero norm and half-trace at this positive index
   are the original `SeventeenScalarDepth318.norm_ne` and
   `.half_trace_ne`, not values at a zero index.
2. Choose the **single J after that same h_base**, by the exact
   proof of `FiniteScalarCenter318.label`. At 131 request
   v_p(I)≥v_p(H)+1, where I is the actual
   `ActualScalarRoot318.inverseNorm n`. The arbitrary-depth
   `GeneralScalarDepth318.scalar_label` achieves this for
   every nonzero free d after using the product J of label
   moduli. Keep the anchor exponent N=2^16 and
   n=`ScalarPreparedResidues318.scalarLabel 0 0
   (PreparedAnchorLabels318.multiplier (2^16) (J*d))`;
   in particular it is legitimate to set d=1. This keeps the
   original 6-power, 3-power, explicit sign branch, and Lucas
   labels. Other support primes retain the strict depth
   inequalities of the original packed-unit proof.
3. On that exact base index and exact fixed labels, the stored
   leaves are H,f above by `ScalarActualInputs318.detector33/37`.
   Since R is a 131-adic unit, N_pack=1+(H/R)²+2f/R
   is 1 modulo 131²; Q=I/(H R^15) lies in 131 Z_131.
   Therefore W=N_pack²+R Q² is 1 modulo 131². At the old
   support primes the unchanged `ScalarPackedLocalUnit318.actual_unit`
   gives the exact W units used by `AllScalarSupportPreparation318.prepared_of_units`.
4. Preserve all the W units AND this congruence after labels.
   At 131 apply `ScalarIndexContinuity318.actual` using
   `AllPrimeSourceProgression318.actual_chart`, then
   `LocalIndexRegularity318.nat_progression` for the open
   131-adic ball about W(h_base) of radius 131^−2.
   Its integer index progression ensures W(h)≡1 mod131².
   Multiply that positive modulus into the old support-unit
   modulus, also keeping 64 and M_base. The ordinary
   `AllScalarSupportPreparation318.Prepared` now holds
   on the same combined progression; the extra 131 condition
   holds as well, without asking 131 to support A.
5. Run the exact real `JointSmallPrimePreparation318.adjust_center`
   inside this combined progression. It supplies a positive
   h₁>1 with all original guards and the actual strict 1/100
   norm margin (not merely a chart denominator nonzero).
   The scalar `PreparedIntegerSource318.scalar_domain` now
   makes b positive and <17 (in fact <1/10000 as before); the
   original prepared scalar lifts to the literal Ready b.
   This alone proves actual arithmetic existence of an allowed
   scalar b with the stated 131-component of theta, unconditionally
   of the shared Gaussian prime tuple.

If the three detector neighborhoods are needed, retain that
same combined progression in `AllScalarDetectorJoin318.join`
(which chooses a real center then a multiple of its old modulus).
The real/Gaussian family is then selected at the resulting L in
the usual order and its congruence preserves 131. The detector
prime tuple and its mapped t are not produced here and retain
their original separate input. Thus this condition is compatible
with the phase of the joined proof; it is not a claim that the
full prepared ordered quartet was already realized.

Exact source pins (SHA256 prefixes): GeneralScalarDepth318
4ff48076; FiniteScalarCenter318 c0a26827;
ScalarIndexContinuity318 16507d42; LocalIndexRegularity318
06f35c46; AllScalarSupportPreparation318 db7793cd;
JointSmallPrimePreparation318 a592270f;
AllScalarDetectorJoin318 36f345e2; PreparedIntegerSource318
e3ecec83. These are cited proof statements, not new hosted
kernel acceptance for the strengthened proposition.

## Exact finite dual-candidate consequence

For this a=0, β=204618888056724185 with support
5,11,17,163,661,733,1489,1861. At 131, β≡27=17². Write the
actual c=C/Z in lowest terms, βc²=b/17, and H0=Z²−βC².
Both C,Z are 131-units (βc²≡1), with v_131 H0=1.
The literal specialized E,E' from FINITE-SPECIALIZATION-SELMER-TEST.md
therefore have split multiplicative fibres I4 and I2.
Every dual isogeny Selmer candidate d' must be a unit with
Legendre symbol +1 at 131. The complete sign row on the
fixed known support is

    class    -1   2   3   5   11   17   163   661   733   1489   1861
    bit       1   1   0   0    0    1     1     1     1      0      0

where 1 is nonsquare. Thus in the span on this support the
row excludes exactly the classes with odd total exponent
on −1,2,17,163,661,733. If a candidate has extra factors
from C or 25βC²−9Z², their actual symbol bits must be
included; this is one exact linear row, not a full
dual-dimension bound. Theta on the source E is locally
allowed and has the specified ramified nonsquare-unit
class, so the dual exclusion does not obstruct theta
there.

No actual h has been materialized numerically and no
finite specialized global point, rank, or Sha conclusion
is inferred from this exact local information.
