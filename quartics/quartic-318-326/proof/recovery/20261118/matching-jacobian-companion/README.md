# Explicit rational Jacobian of the matching cover, with a second all-place choice

Use the same original prepared β,θ,B,V and e(t) as forward-all-pole-fixed-matching-cover-r1. Here k is either 4 or 12, m=βk², C=θ(1−m), φ(t)=(t+k)/(1+βkt). Let

    Hₖ : y²=C(1−9βt²)((1+βkt)²−9β(t+k)²).
    r₁=βC(25m−9),    r₂=16βCm.
    Jₖ : Y²=X(X−r₁)(X−r₂).

The second choice k=4 preserves global marking and gives another fixed everywhere locally soluble 2-cover for every prepared b. The following calculation identifies which of the split Kummer classes represents each cover: with coordinates ordered X,X−r₁,X−r₂ its triple is **(1,β,β)**. No global lift follows solely from this identification. This explicit input allows actual Cassels pairing tests on these particular classes.

## Birational isomorphism after the quadratic extension

Work over K=Q(√β), putting z=1/(3√β), α₁=z, α₂=−z, α₃=φ⁻¹(z), α₄=φ⁻¹(−z). The four branches are finite distinct since m∉{1,9,9/25} (β is nonsquare). The quartic on the right is g∏(t−αᵢ), g=−9Cβ²(m−9). For u=1/(t−α₁), w=yu² its cubic has leading coefficient A=g∏_{i=2}⁴(α₁−αᵢ) and roots uᵢ=−1/(α₁−αᵢ). Put X=A(u−u₂)/4 and Y=A w/8. The three roots are exactly 0,r₁,r₂: indeed

    4r₁=A(u₃−u₂)=g(α₁−α₄)(α₂−α₃),
    4r₂=A(u₄−u₂)=g(α₁−α₃)(α₂−α₄).

These equalities follow by substituting α₃=(z−k)/(1−βkz), α₄=(−z−k)/(1+βkz); the forward rational map is an isomorphism of smooth projective models, with inverse u=u₂+4X/A, t=α₁+1/u, y=8Y/(A u²). R₁,R₂ above α₁,α₂ map to O,(0,0). The invariant differential pulls back as dX/Y=−2dt/y, unchanged under conjugation. Therefore the conjugate choice differs by translation, not by a nontrivial origin-preserving automorphism (characteristic zero). Comparing the images of the conjugate R₁,R₂ shows that this translation is exactly T₀=(0,0). Hence Jₖ is the actual rational Jacobian, rather than a twist inferred from a j-invariant. In this identification the full covering Hₖ→Jₖ is P↦[2P−D∞], with D∞ the degree-two fiber of t: over K this is doubling after using R₁ as origin. Its cocycle is χβ times T₀. For split Kummer coordinates the Weil pairing of T₀ with itself is +1 and with each other nonidentity root is −1, giving (1,β,β).

## The new k=4 completion at 3

The k=12 uniform local proof carries over at all places except possibly 3: at 2, k=4 still gives 1−m and 1−9m square, and all finite odd primes outside 2·3·βθ with determinant or branch collision force β locally square (the only extra primes dividing k are 2). At 3 if β is square take a branch; if 3|β then θ square by preparation and t=0 works. Otherwise β≡2 mod3; θ is a square since D≡1. Choose integral t with 1+βkt of valuation one, possible by CRT on t mod9. Then m≡2, t+k is a 3-adic unit (in fact (m−1)/(βk) mod3), and q₁≡1. Moreover q₂/9≡1−β≡2 and C≡2 modulo 3, so the radicand has square class 1. This gives the missing completion. All real places are handled by the four real branches. Thus the explicit (1,β,β) class lies in Sel₂(J₄/Q) and Sel₂(J₁₂/Q). A global lift on either is enough for literal PointPair. Local conditions do not select the globally successful curve.

## Reproducibility

The exact substitutions are checked in verify.py with elementary arithmetic in Q(√β), no floating point or CAS. See REPLAY.json. Compare the parent packet and the common source commit a0950ac7c24df6d336a196966fb790d6abd55e44; these are mathematical proofs and rational controls, not a Lean run. This packet is an input to separate Cassels row certificates, not their proof and not an assertion of any indexed global rational lift.
