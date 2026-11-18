# Both analytic root signs on full matching-cover Jacobians at the same actual indexed pole

For the exact scalar pole of the a=0,−1 original integer index, the k=4,12,16,48 families all have an everywhere locally soluble marked matching cover for the original pair. Keeping the pole *fixed*, the analytic functional-equation signs of their four different Jacobians are respectively

    k      4   12   16   48
    sign  +1   +1   −1   −1.

In particular J₁₆ and J₄₈ have odd analytic rank, at least one unconditionally. This is an arithmetic computation on the actual indexed twists by θ, not on a synthetic value, and does not require factoring θ. It is **not** a claim of positive rational rank, analytic rank exactly one, nonvanishing derivative or global lifting of the marked cover. A positive rank on J by itself would not identify the required Selmer coset.

## Curves and twist data

Use h=328655617654071015360, m_ind=6²¹·3⁶⁵⁵³⁶ h g⁸·11·17, g=1094218652709755, r=4g, β=204618888056724185 and θ representing the true D=1−b/17; see the exact source trace in db5260f384db48f1cc58f96a88ea97de1f6c388697d0b9e3546bb15886fe8c9f. This β is 1 mod8, 2 mod3; θ is positive squarefree, 1 mod8 and square locally at 2,3 and primes dividing β. For the base curve write

    M=βk², r₁=β(1−M)(25M−9), r₂=16β(1−M)M.
    J₀:Y²=X(X−r₁)(X−r₂).

The target J is its θ-twist with roots 0,θr₁,θr₂. The geometric identification is the rooted quartic change in the preceding matching-jacobian packet, valid at all these k. Its associated full 2-cover Hₖ has local points by the same proof: 4|k, so t=0 at 2,p|β, and at 3 either 3|k and t=0 works, or k is a unit and θ(1−M)≡2 permits integral t with v₃(1+βkt)=1. At p≥5 extra singularities require M=1 or 25M=9 modulo p, so β is a square and a branch works. The support of every k here is contained in {2,3}. Existence of rational points on H remains open.

## True-orbit residues, including bad reduction above 7

INPUTS.json and original_probe.py certify every nontrivial baseline residue used below by original division-polynomial evaluation and complete Lucas primality trees, as in forward-indexed-complement-selmer-ramification-r1. The original ψ_M=0 with unit numerator check removes any reliance on CM conjectures or guessed group orders. If hP is formal at 31 or at one split component of 7321, the required U² ratio has residue (m_ind/h)² by its formal leading coefficient; all these local tests use precision one. At 29 if needed the prior all-index obstruction would give [θ]=[17], but no such substitution is required in these four check tables.

The original generator's model has bad reduction at one 7-adic embedding, so do not apply a good-reduction order formula there. At √2≡3 mod7 the primitive R=(4,6) lies in the smooth locus of y²=x³, the additive group of order 7. Since h≡m_ind≡3 mod7, both 2hR and 2m_ind R reduce to −R, a finite point with x=4. Thus U_h²≡U_m²≡2 there. At the other embedding the original j=1728 model has good reduction, order eight over F₇ (the sum for y²=x³−δx vanishes by x↔−x). Since 8|h, hP and m_ind P are formal, U_h²≡0 and U_m²/U_h²≡(m_ind/h)²=1 mod7. With r≡A≡3 mod7 this gives N=4,Q²=1,W=5,D=6 mod7. The full verified table now shows θ is a unit class at every prime of every baseline conductor. The computed table normalizes D only up to local square, which is exactly what an unramified quadratic twist uses.

## Direct local root numbers of J₀ and J

For clarity the signs are derived from the local models, not assumed from an analytic-rank program. At odd p≥5 use the standard local root-number formula: multiplicative reduction has sign −1 if split, +1 if nonsplit; ramified quadratic twists of multiplicative reduction (type I*_n, n>0) have conductor exponent 2 and sign (−1/p); a ramified quadratic twist of good reduction likewise has sign (−1/p) at p≥5. See J. Desjardins, [Root number of twists of an elliptic curve](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.1112.pdf), local formulas. An unramified quadratic character multiplies the sign by its Frobenius value to the conductor exponent; for these multiplicative fibers this simply swaps split and nonsplit. The elementary reductions are as follows.

* At 2 make the integral change x=4X, y=8Y+4X. The resulting equation is Y²+XY=X³−(1+r₁+r₂)X²/4+r₁r₂X/16. Both displayed coefficients on the right are even (β≡1 mod8, 4|k). The reduction Y²+XY=X³ has a split ordinary node at the origin, conductor exponent 1 and sign −. The twist by θ is trivial locally.
* At 3, if k is a unit, both nonzero roots are 2 modulo 3. The nodal tangent is nonsplit (2 nonsquare), exponent 1 and sign +. For k=12,48 divide the roots by 9 using square-scaling. The three roots are then distinct mod3, giving good reduction. θ is locally square in both situations.
* For p|β, p≥5, the three valuations of the nonzero roots and their difference are 1,2,1. Removing the ramified twist p gives roots of valuations 0,1 and a unit difference, hence multiplicative reduction. For J₀ the exponent is 2 and sign (−1/p).
* For p≥5 dividing M−1 with valuation e, both roots have valuation e and their difference has valuation 2e. After dividing by p^e the two roots reduce to the same nonzero unit a. If e is odd the original is a ramified twist of a multiplicative curve, with the preceding exponent/sign. If e is even this is an integral square-scaling with ordinary nodal tangent slopes ±√a; exponent 1, sign −(a/p). This includes the repeated factor 7² at k=16.
* If p≥5 divides 25M−9, outside the prior cases, r₁ is zero and r₂ nonzero modulo p, giving an ordinary node with tangent squareclass −r₂. Exponent 1 and sign −(−r₂/p). All remaining baseline primes are good. These lists are exhaustive by r₁−r₂=−9β(1−M)².

Thus θ is unramified at the baseline conductor. At its own distinct prime factors, all away from 2,3 and that conductor, the product of the new local signs equals ∏(−1/q)=+1 since θ≡1 mod4. Include the same archimedean − sign on each curve. verify.py multiplies the resulting factors from the exact input D residues. For example at k=16 the baseline sign is −, and among its exponent-one primes 2,3,7,571,773,2437,7321,166296901 the four nontrivial unramified characters occur at 7,571,7321,166296901. The true twist therefore retains the odd sign. The baseline signs for k=4,12,16,48 are −,+,−,+; the twist multipliers are −,+,+,−. Analytic continuation and the functional equation for elliptic curves over Q follow from modularity, so the two negative signs give zeros at the central point without an arithmetic-rank assumption.

Run python3 -B verify.py and compare REPLAY.json. All computation is stdlib arithmetic with exactly verified primes and annihilators. Source commit a0950ac7c24df6d336a196966fb790d6abd55e44; mathematical proof and tests, not Lean. No new point count or claim of resolution of any of the four missing second-square rows.
