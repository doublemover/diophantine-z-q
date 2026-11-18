# No original scalar numerator, at any integer input, is a sum of two rational squares

This is a statement about the *actual* scalar numerator, independent of choices of the common index, chart or complementary squareclass. Let R=ScalarPolePreparation318.integerR(a). The exact source identity ScalarForwardWitness318.pole_squareclass_eleven gives
    b=(11R)·(102·quotient)²
on the source scalar slot. At a nonzero prepared pole the positive squarefree representative β of B=17b is therefore sf(17·11·R). For EVERY integer a this β has at least TWO distinct primes 3 mod4 in its support. Consequently it is not a sum of two rational squares. The positive c=β matching-Jacobian circle of the ray proof is impossible for the original scalar at *every* integer input, not merely the explicit scalar β(0). This does not obstruct other c, all other local constructions or the original PointPair.

Original source pin a0950ac7c24df6d336a196966fb790d6abd55e44, quartics/quartic-318-326/proof/experiments/forward-actual-ambient-primitive-lifts-r1: ScalarPolePreparation318.lean sha256 721851a467f0e8f34e4e6cb267aae94af3bf9da73e1c570d332c7f0b3c85ee10 and ScalarForwardWitness318.lean 115729a9f8748290186bb0396ed78dd0355ec3fd93ff8a7ffb02f653dad675a5. integerR_cast is the literal rational/integer comparison.

## Separate the only possible shared bad primes

Put t=a(a+1), a nonnegative even integer, and
    U=7446t+661,    V=7446t+1861,    W=29784t+7445,    Z=476544t+119479.
Direct coefficient comparison gives the polynomial identity R=4UV WZ. The first three factors are positive and 1 mod4; the last is positive and 3 mod4. No factor is divisible by 3. Neither W nor Z is divisible by 11: their affine roots modulo 11 would require t=5 or 7, respectively, neither in {a(a+1) mod11}={0,1,2,6,8,9}.

If a prime divides two affine factors, it divides their determinant (slope times intercept minus intercept times slope). Factoring the five determinants needed for W,Z gives the following exact restriction on shared primes congruent 3 mod4 (exclude 3, already impossible):
    W with U: none;     W with V: none;     W with Z: only 359;
    Z with U: only 7;   Z with V: none.
Indeed det(U,W)=2·3·17·73·4801 and det(V,W)=2·3·17·73; det(W,Z)=2³·3·17·73·359; det(U,Z)=2·3³·5²·7³·17·73 and det(V,Z)=2·3²·5³·17·73. Here 4801 and 359 are prime. Thus no hidden shared prime could carry one of the odd exponents below.

The 7 edge cannot cancel an odd valuation of Z, because v₇(U) is ALWAYS even. Exactly
    2U = 3723(2a+1)²−7⁴,     3723≡−1 mod7.
If 2v₇(2a+1)≠4 the two valuations are unequal and v₇(U) is their minimum. If equal, divide by 7⁴ and reduce: −s²−1 is nonzero modulo 7 for the resulting unit s, since −1 is nonsquare. Thus v₇(U)=min(2v₇(2a+1),4) in all cases.

## Parity contradiction and the actual geometric consequence

Suppose every prime 3 mod4 occurred to even exponent in 17·11·UV WZ. Any such prime occurring to odd exponent in W must also occur in U,V,Z or 11. The only candidate is 359. But W≡1 mod4, so the number of its 3-mod-4 prime divisors with odd exponent is even. Thus W has no such prime, in particular v₃₅₉(W) is even. Now Z≡3 mod4 forces at least one such prime with odd exponent. It is not 11. Only 7 (with U) or 359 (with W) could cancel it; the valuations in those other factors are even. Contradiction. Moreover 17·11·UV WZ≡1 mod4, so an EVEN number of distinct 3-mod-4 primes have odd exponent in it. There must therefore be at least two. These are also odd-exponent primes in the actual β. The proof even locates at least one in the union of the supports of W and Z; it does not designate the same fixed prime at every integer a.

For any prepared nonzero scalar b write 1−b/17=θz² and b=17βr². Thus θ is a norm squareclass from Q(√β), independent of the choice of its representative. Also 1−βk² is a norm from that field. If a rational k made θ(1−βk²) have squareclass β, β would have to be a norm. Since −β=Norm(√β), this would make −1 a norm: x²−βy²=−1. Then β=(x/y)²+(1/y)² (y≠0), contradicting the odd valuation at one of the proved 3-mod-4 primes: the valuation of a nonzero sum of two rational squares at such a prime is even, by the nonsquareness of −1 in its residue field. This directly rules out every positive-circle slope on every original scalar, without any BSD, prime-pattern or global finiteness assumption. It explains why the ray criterion cannot simply be extended to a better choice of scalar input. It does not rule out globally successful scalar twists or a different scalar companion. No Lean elaboration.
