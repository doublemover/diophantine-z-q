# At the unchanged ray pole: exact control of local solvability on the positive-rank circle

Use positive, disjoint squarefree β,θ, β=17 times the true ray primes 1 mod408 (the argument also covers β=17). In particular every p|β is 1 mod8, p≠5, β≡17 mod24, θ≡1 mod24. Keep the specified b=17βr², 1−βr²=θz² and its complete complement, not a nearby b. Then θ is square locally at p|β, and β locally square at p|θ as in the primitive conic calculation. Let
    η=∏_{p|β}(θ/p)₄=(ℓ/β),
where ℓ is the true reduced denominator of r and the square-root quartic character means +1 for a fourth power, −1 for a square not a fourth power mod p. The equality with the earlier relative genus bit uses the same primitive input conic.

The positive-rank circle consists of rational (k,h) satisfying 1−βk²=βθ h². Its existence and infinitely many slopes at this same b were established by the sum-of-squares transformation in the coefficient packet. For each such k the actual matching Jacobian is rationally isomorphic to F_m:Y²=X(X−a)(X−d), m=βk², a=25m−9, d=16m. The class ε=(β,1,β) is globally represented by the explicit nontorsion (25m,45m). The original matching class remains δ=(1,β,β), in these same ordered slots.

**Exact local test.** Write k=n/(βD) in lowest terms with n nonzero, D>0. This is legitimate because every p|β has v_p(k)<0. Then δ belongs to Sel₂(F_m/Q) if and only if EVERY odd prime dividing n is split in Q(√β). A single inert numerator prime obstructs the actual matching quartic at that place, even when its exponent is even. No condition concerning primes whose product happens to be a norm suffices.

**Uniform consequence at fixed b.**
* If η=−1, every positive-rank circle slope fails this local test, and at least one nonsplit numerator prime gives a witness.
* If η=+1, there are infinitely many slopes on the circle (infinitely many distinct geometric j-invariants) with δ genuinely in the full 2-Selmer group, alongside global non-torsion ε on the unchanged b. This does not assert δ lifts globally: that would require a specialization jump to rational rank at least two. The same circle has geometric generic rank only one.
* For either sign we can choose n to consist of a single NEW positive prime. Thus for η=−1 one can arrange that this varying prime is the **only** local obstruction, away from any prescribed finite set. These statements do not select a successful literal PointPair, nor apply directly to scalar β with a 3-mod-4 factor.

## Every local place on the circle

If β is a local square then δ is the trivial squareclass. This includes the real place, 2 and all p|θ. If p|β, then v_p(k)<0: otherwise 1−βk² is a unit square but βθ has odd valuation. Here v_p(m) is negative odd and a∼d∼m∼β in squareclasses (p≠5). The root T₀ has slots (ad,−a,−d), equal to δ since −1 is a square. At 3, β is a nonsquare unit and θ is square. The circle equation rules out v₃(k)>0 (1−m would be square) and v₃(k)<0 (1−m would have class −β, a square at 3). Thus m≡2 mod3 and a≡d≡2 mod3. Taking X=1 gives exactly δ.

Let p≥5 with β an unramified nonsquare and p∤βθ. If v_p(k)=0 then the roots a,d,a−d=9(m−1) are units: 25m=9 or m=1 in the residue field would give β square (25m=9 impossible when p=5). Good reduction and the unit-valued unramified Kummer classes give δ locally. For v_p(k)<0 rescale roots by k², obtaining a'=25β−9/k², d'=16β. For p≠5 these and their difference are units, again good. At p=5 the only potential exception is actually soluble: a'/25 is a 5-adic unit, including when v₅(k)=−1 because β is nonsquare. Choose integral s,t solving s²−βt²=a'/25 by unit-norm surjectivity in the unramified quadratic extension. We may perturb the local conic point off zero coordinates. Set X'=25s²; its first two slots have classes 1 and β, and X'−d'≡−16β mod5 gives third class β since −1 is square at 5. Thus no denominator prime obstructs.

If v_p(k)>0 instead, the second Kummer slot is ALWAYS square. At nonroot abscissas with v(X)>0, X−a≡9 mod p. With v(X)≤0 the numbers X−d and X have the same squareclass, so the cubic equation forces X−a to be square. This covers roots and infinity by local constancy of the Kummer map and density of nonroot points in local smooth neighborhoods. Indeed the integral projective δ cover already has NO point modulo p: X₁²−βX₃²=0 forces X₁=X₃=0, then βX₂²=9T² forces X₂=T=0. These cases prove the exact test.

## The old quartic bit controls every new numerator

Set H=βD h. The equation is
    n²+θH²=βD²,    gcd(n,βD)=1.
H is integral since θ squarefree and θH² integral. Then gcd(n,H)=1, gcd(H,β)=1. Mod p|β we have n²≡−θH². Because p≡1 mod8, −1 is a fourth power; taking the quadratic character of a square root yields
    (n/p)=(θ/p)₄(H/p).
The product (H/β)=+1: any odd q|H gives n²≡βD² mod q with n,D units and hence (β/q)=1. The factors of 2 and sign in H have character +1 at β, and all p|β are 1 mod4 so reciprocity gives the product. Consequently (n/β)=η. Every inert odd prime factor of n contributes −1 per odd exponent to this Jacobi evaluation and a separate local obstruction irrespective of exponent. In particular η=−1 forces failure.

## A single new prime as numerator, with the required sign

Start with any rational point on the circle, known to exist, and use weak approximation on this rational conic to arrange k a unit at 2 and every q|θ. At 2 this local open condition exists: β and θ are 2-adic squares, and in 1/β=k²+θh² choose h nonzero sufficiently small. At q|θ take h small and use that β is locally square. At real places one has 0<|k|<1/√β and can avoid zeros. Thus the initial reduced integers n₀,H₀,D₀ also satisfy gcd(n₀,2θ)=1. From the norm parametrization
    (n₀+H₀√−θ)(X+Y√−θ)²=F+G√−θ,     D=D₀(X²+θY²)
one gets
    F=n₀X²−2θH₀XY−θn₀Y²,       F²+θG²=βD².
F is a properly primitive indefinite integral form: gcd(n₀,θH₀,θn₀)=1 (indeed n₀ is odd) and its discriminant 4βθD₀² is positive nonsquare. By the classical theorem on primes represented by a properly primitive binary quadratic form, it represents infinitely many positive primes P outside any finite excluded set. See [Briggs, An elementary proof of a theorem about the representation of primes by quadratic forms](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/52E50F7ED4AF4D35D1D2EE52AA141903/S0008414X00023786a.pdf); the positive nonsquare determinant case here is the indefinite case in the paper's sign convention.

Exclude all primes dividing 2βθD₀. For F(X,Y)=P we have gcd(X,Y)=1. If P also divided D, then X²≡−θY² mod P with Y≠0. Substitution into F yields n₀Y+H₀X=0 mod P, hence n₀²+θH₀²=βD₀²≡0 mod P, excluded. Thus k=P/(βD) is reduced and has unique numerator prime P. Its splitting in Q(√β) is exactly (β/P)=(P/β)=η. The local test above proves that at η=+1 every such P gives a genuine everywhere-soluble marked H, and at η=−1 P and only P obstructs. Different P give different k, hence infinitely many geometric j by the finite-fiber formula. This uses a binary form prime theorem in TWO variables, not an unproved prime-values hypothesis for univariate polynomials.

The companion exact replay uses explicit original-type sample conics (β,θ)=(17,409),(17,457), proves the new one-prime, no-cancellation, split/inert labels and independently checks finite odd local Kummer images at selected challenging places by actual projective representatives or valuation arguments. The small controls are stand-alone and do not claim a numeric 15-label indexed assignment. No local Lean elaboration.
