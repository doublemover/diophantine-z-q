# A fixed-index obstruction on the original three literal detector poles

This uses the same coefficients and same h,t in stored slots190,241,292.
It applies to the actual retained scalar progression, but needs no
new choice of h, t, labels, or prime-pattern coefficients. It is a
necessary condition on a direct rational PointPair, even before
requiring the named prime-pattern/Ready proof. It is not a claim that
any of those three slots has no rational witness.

## 1. Odd negative valuation forbids any literal PointPair

Take b∈Q^× and a NormalizedPolePoints318.PointPair b, retaining
its one parameter λ and scale s≠0. Write

    B=17b, r=λ/B, δ=1−b/17, V=B²δ.

Divide the two equations by B² and (Bs)², respectively. Their
right sides become

    B(1−r)(1+3r),       B(s²−rV)(s²+3rV).

Let p≠3,17 and suppose v_p(b)<0 is odd. Both v_p(B) and v_p(δ)
are that same odd value. Necessarily r is a unit: for r=0 or
v_p(r)>0 both first factors are units, and for v_p(r)<0 both
first factors have valuation v_p(r). In either case that first
nonzero right side would have odd valuation. With r a unit,
v_p(rV) is odd, so differs from v_p(s²). Both second factors
have the common valuation min(v_p(s²),v_p(rV)), because 3 is
a p-unit. That second nonzero right side would have odd
valuation, a contradiction. The two ordinates were permitted
to be zero; that possibility does not help at the step that
has nonzero odd RHS. This also proves the obstruction over
Q_p and includes p=2.

The restriction on p is meaningful: at p=17 take b=1/17,
λ=0,s=1 and y₁=y₂=1 (a literal rational pair); at p=3 take
b=−1/(3·17), r=1/9, s=1. For the latter choice B=−1/3 and
V has v₃=−3, so each right side equals an exact square r²
or (rV)² times a product of units in 1+3 Z₃. Both are squares
locally despite the negative odd valuation. The original
Ready guards already take care of these exceptional places.

## 2. Exact leading term of the original 16-leaf fold

Fix the original a, labels and a guarded h with nonzero chart norm;
write w=DetectorGateWitness318.witness a labels h. For one actual
detector, use the exact scale c from ThreeDetectorArithmetic318.scales,
T=c²t, Δ=T−1, F=contact(T), and the selected fold view. The shared
contact polynomial is precisely

    F(T)=T(T+1/2)(T+1)(T−1/2399)(T+32/407).

Fix odd p with c and Δ p-units, and put e=v_p(F)>0. The three
weights used by the actual fold have valuations −e,−7e,−25e.
In the original order the weights are
7,1,1,1,1,1,1,1,1,1,7,25,25,25,7,25, where each integer is
the indicated exponent on the scaled weight. The first coefficient
is the rational w37², since DetectorGateWitness318.value126 is
literally w37². Each other coefficient is a fixed element of
Q(√2) at this h, independent of t; only the rational weight changes.

In the free rank-two ring O=Z_p[√2], suppose all coefficient
coordinates are integral and w37 is a p-unit. After the first
leaf the running value is p^(−7e) times an O element with
nonzero *scalar* leading residue modulo p; the initial value is 1
and the first coefficient is scalar. The second leaf has lower
valuation bound −e, strictly above the squared leading value
−14e. At every step from the third onward, the leaf bound is
−25e, strictly above the next squared leading value ≤−28e.
Thus the final X=Re(X)+Im(X)√2 is p^(−M) times an element of O
with scalar unit reduction and imaginary coordinate in p Z_p,
where M=7·2^15 e. This argument neither chooses an embedding nor
assumes p split. Consequently Re(X) and Norm(X) have exact
valuations −M and −2M. The literal trace quotient Norm(X)/(2 Re(X))
has valuation −M. The stored detector equals this quotient squared
times F/(c^10 Δ^6), also at scale c=1 by stored_pole. Hence

    v_p(stored pole)=e−14·2^15 e=−458751 e.

Odd positive v_p(F) is therefore fatal for a PointPair whenever
p≠3,17 and these stated coefficient guards hold.

An actionable variant allows coefficient denominators. If all 16
coefficient coordinates have lower bound −K, K≥0, and d=v_p(w37)
is finite, it is enough that 3e>8 max(0,d)+K. Replace 7e by
ρ=7e−2d>0. At step 2 require 2ρ>e+K; at step 3 require
4ρ>25e+K. The single stronger inequality ensures both, and all
later squared values dominate even more. Then the precise answer
is e−2^16ρ<0 with the same parity as e. This is a finite p-adic
rejection certificate at the literal h, not an elliptic-rank test.

## 3. Global meaning for fixing h before choosing t

For fixed h and fixed nonzero labels, there is one finite exceptional
set S: include 2,3,17; primes at which the selected fixed scale or w37
is not a unit; coefficient denominators of the fold; denominators of
F and the prime divisors of the numerator of F(1). All these
constants precede t. Outside S if v_p(F(c²t))>0, the monic integral
polynomial forces c²t integral and outside the residue 1, so Δ is a
unit. Thus any positive odd contact valuation outside S rejects the
same literal pole, regardless of the other two detectors.

If t has reduced square denominator, as for a primitive u/d²,
its negative valuations are even. For p outside S with v_p(c²t)<0,
monicity then gives v_p(F)=5v_p(c²t), even. For integral c²t the
contact valuation is nonnegative. So all allowed nonzero contact
values have rational squareclass supported in S. With this one
fixed h, every t passing the PointPair requirement for even ONE
detector lies in the image of a finite union of

    F(c²t)=d z²  (d a signed squarefree product of primes in S).

Each is a smooth genus-two hyperelliptic curve after projective
normalization: five distinct roots and infinity branch. Thus the
set of such rational t is finite by Faltings (1983,
[original paper](https://geodesic.mathdoc.fr/item/IM_1983__73_143051/)).
No effectiveness or bound on the size of S is claimed. If t is not
required to have square reduced denominator, only the positive
odd contact valuation obstruction was proved, not this finite
union. This does not contradict the source: the original mixed
CRT moves h *after* obtaining the contact support. Its local primary
entries deliberately move w37 away from the unit-leading regime.

## Literal source pins and controls

Pinned source copies are in the original
forward-actual-two-descent-root-divisor-orders-r5 experiment.
Relevant exact SHA-256 prefixes: NormalizedPolePoints318 410995ba,
ActualDetectorFold318 1bb3b85f, DetectorGateWitness318 5c6c6153,
ScaledContactWeights318 75a17ba0, ScaledDetectorChain318 6b40c470,
ThreeDetectorArithmetic318 6afbbd9c. All claims above concern
these literal formulas, but no Lean run or source mutation was made.
The exact adjacent checker uses synthetic coefficient coordinates
to stress-test the Laurent leading-normalization argument over
odd residue rings, including both w37 unit and nonunit and
negative coefficient depths. These are not numeric h evaluations.

```sh
python3 -B check_contact_leading.py | cmp - EXACT-CONTACT-LEADING-CONTROLS.json
sha256sum -c SHA256SUMS
```
