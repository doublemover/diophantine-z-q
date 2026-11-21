# Explicit shared detector prefix at the fixed retuned scalar h,J

This closes a **partial** same-index producer without choosing
any Gaussian primes. It keeps the original row coefficients and
scalar b, constructs labels and one common contact t for all three
literal pre-poles, and proves their real bounds and actual 2,3,17
local conditions. It does **not** assert that their reduced
denominators are squares or that any of the four PointPairs exist.

## The exact retained h,J and a computable choice of labels

Use a=0, A_label=B_label=0, N₀=65536, d=1, and the h,J from
the actual q1041427 prefix JSON SHA-256 5a70adc6…. Set
i=6^15·3^65536 J, s=1+i, k=2(s−2) and choose

    n = (3723, s, U_s(k+1), U_s(k)/(s−2)),     U_s(0)=0, U_s(1)=1,
    U_s(r+2)=sU_s(r+1)−U_s(r).

These are permitted witnesses for the same original four
labels, not an assertion about which witness an opaque
Classical.choice picks. The positive odd and literal Lucas
equation checks are exactly positive_odd_witness_at_index
at the concrete k in LucasWitness318. The integrality is
(s−2)|U_s(k) from U_s(k)≡k mod(s−2). Here s≥3, s is odd
with s≡1 mod3, k≡4 mod6, and N₀≤v₃(s−1). Both extra
labels may be kept as exact circuits. For modular evaluation
of n3 at l^a where l|s−2, compute U_s(k) modulo l^(a+v_l(s−2))
by the 2×2 recurrence matrix, remove the certified l-power
before inverting the remaining denominator unit.

At p=5 R has exact order 5, h and i are both divisible by
5, and s≡1 mod5. The period-six reduction of the recurrence
gives n=(3,1,4,1) mod5. The two endpoints n_j h and n_j(h−1)
therefore give rational guard residues (4,1,1,1), respectively.
The independent small checker derives these using the actual
quadratic generator and the literal chart, not a sign proxy.
It also verifies the two retained scale roots mod1041427
are 827917,813982: both are units there. At 5 the roots are
0,4 mod5, respectively; that is only a local scale value.
The already certified outward real norm of the same h gives
the strict scalar margin. No positive real sign of all four
guard values is needed for the direct completion endpoint,
only the nonzero guards just checked.

This choice **does not change the scalar b**. The source
ScalarActualInputs318.detector33 and .detector37 make the
other two chart arguments of ScalarForwardWitness318.W
independent of n₂,n₃; the scalar retains s as its one label.
PreparedIntegerSource318.complete_at_index is parametrized
by the actual nonzero labels and does not demand a
Classical.choice identity. Its anchor is attainable on this
same n too: use ActualAnchorRatio318.local_depths at N₀
with these odd labels and demonstrated scalar depth, then
ActualAnchorTwoConics318.residue and .bind with the independently
proved ActualPreparedAnchor318.pair at that reduced integer.
PhysicalAnchorFromHomogeneous318.currentAnchor uses the
same n at the literal current S. No new anchor premise or
change to any raw row coefficient is needed.

## One constructive rational square t for the real and small local gates

Fix w=DetectorGateWitness318.witness 0 n h and all three
literal scales c_j from ThreeDetectorArithmetic318.scales.
They are nonzero by the existing fixed-scale lemma. Write
X for the quadratic-algebra fold after all 16 leaves with
the actual view at c,t; let τ=N(X)/(2 Re(X)). For one scale
put r=1/t, T=c²t, u=1/T and define

    f(u)=(1+u/2)(1+u)(1−u/2399)(1+32u/407).

Thus F(T)=T⁵ f(u) and Δ=T(1−u). Direct substitution into
the exact original weights w151,w156,w158 gives

    c⁴ r³ (1−u)^2   / f(u),
    c⁶⁴r³ (1−u)^32  / f(u)^7,
    c²⁴⁴r³(1−u)^122 / f(u)^25.

The literal stored pole, including at scale one, is

    4 c^12 t b = (2τ)^2 f(u)/(1−u)^6.                 (*)

This uses no norm comparison, prime support or change of a
rational witness at another detector.

For p∈{2,3,17}, let a_p=max_j |v_p(c_j)| and let b_p≥0
bound from below the valuations of **both coordinates**
of each of the 16 fixed fold coefficients by −b_p.
Zeros need no bound. Let d_p≥0 bound the denominator
valuation of each coefficient after 1 in the four factors
of f(u). Put e₂=3 and e₃=e₁₇=1, and let A_p be the
requested depths 3,1,2 respectively. Choose an integer m≥1
satisfying all nine explicit inequalities

    2m−2a_p ≥ d_p+e_p,
    6m−244a_p−b_p ≥ e_p,
    2m−12a_p−2 v_p(2) ≥ A_p.

Let D=(2·3·17)^m, choose a positive integer n_R, and take

    R=n_R D+1,                 t=(R/D)^2.

Here R is only the contact numerator root, not the old
scalar input named R. Its coprimality to D makes the reduced
denominator D² and v_p(1/t)=2m exactly. The first inequalities
give f(u),1−u∈1+p^e_p Z_p. The second make all 16 original
leaf products small in the integral pair algebra
Z_p[√2] (no étale assumption at 2 is needed). Iterating
X_k=X_(k−1)^2+leaf from 1 gives X=(1,0) mod p^e_p, so
2τ=N(X)/Re(X) is a nonzero unit. In (*) all factors except
f(u) are rational squares, including 4c^12 t itself.
The unit f(u) is square by Hensel (≡1 mod8 at 2, ≡1 modp
at odd p). The exact pole valuation is
2m−12v_p(c)−2v_p(2), so the third inequalities give
the stated depths for all three poles at the same t.

## Taking the real numerator large does not change those local gates

One can use the pinned real singleton compact-region result, or
the following elementary explicit threshold. Let L≥1 be a
rational upper bound for the absolute values of the 16 fixed
coefficients under both real embeddings, e.g. coordinate bound
|a|+2|b|+1 per coefficient a+b√2. For T≥2,
T⁵/2≤F(T)≤(2T)^5 and T/2≤Δ≤T. The three weights have absolute
bounds 2|c|^4/t³, 2^7|c|^64/t³, 2^25|c|^244/t³. Thus each
leaf product is at most C/t³ for
C=2^25 L max(1,max_j|c_j|^244). If C·3^16<t³, the induction
|X_k−1|≤C(3^k−1)/(2t³)<1/2 for **both** embeddings follows
from |X_(k−1)^2−1|≤3|X_(k−1)−1|. Both fold outputs stay in
(1/2,3/2), in particular their real average is nonzero and
τ=(1/X⁺+1/X⁻)^(-1) is positive and <1. The pole is then
positive and <2048/(|c|^12 t). Choose n_R so that
t>max_j(2/c_j²,2048/(17|c_j|^12),2) and C·3^16<t³.
As n_R increases, the established p-adic conditions persist
since R always stays a unit at 2,3,17. This is an exact albeit
potentially enormous symbolic choice, not an expanded b value.

Now use the unchanged prefix row lemmas: the first detector's
first152 follows from h>1, its actual four nonzero guards,
t>2 and nonzero contact and real part, via
ContactChainWitness318.witness_first150 and
PoleInputFamily318.first152. The exact other two follow via
ThreeDetectorPrePole318.nonpole_rows with c₁,c₂ supplied by
the fixed product identities. This is the unchanged
ThreeDetectorUniformFamily318.witness 0 n h t at the same
three coefficients; actual certificates would still be
needed for the rows between those prefix blocks. In
particular input0 and all literal pre-pole rows hold, and each
of 190,241,292 is positive and <17 and meets the three
required local-square/depth conditions.

## What is still missing

For (p) outside the small prepared places, (*) has factors
whose **odd contact numerator support is not controlled** by
this choice. A square denominator for t is not a square
denominator for any b_j. The fixed-h obstruction dd5d6ca1…
shows explicitly why extra primes matter: for p outside
a finite coefficient set, an odd positive valuation of
F(c²t) gives an odd negative valuation −458751·v_p(F) of
the literal pole and rules out every PointPair. Thus the
all-place denominator/point tasks do not follow from these
real and local constructions. No claim of a joint solved
prime tuple, any rational elliptic pair, or a completed
318/326 row list is made.

```sh
python3 -B check_explicit_labels.py | cmp - EXACT-LABEL-GUARD-CONTROLS.json
sha256sum -c SHA256SUMS
```
