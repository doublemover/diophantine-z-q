# Exact boundary of torsion-based global matching across all slopes

Fix a positive prepared pole with β and θ as in the preceding matching covers, and assume θ>1. For Jₖ, k a nonzero nondegenerate rational slope, let δ=(1,β,β) be the full global marking. There exists some k for which δ is the Kummer image of **rational torsion** if and only if the earlier fixed inversion curve

    A_N: y²=x(x−N)(x−81N),   N=βθ,

has a rational point with [x]=[θ]. Everything in this equivalence concerns fixed b, not an approximating pole or a first-class family. At the 80 residue classes modulo 605, including a=1,3, where the correctly prepared original scalar fails the inversion test even over Q₅, no rational slope in this matching family can succeed through torsion. If Hₖ nonetheless has a rational point its image under the 2-covering on its own Jₖ is forced to be non-torsion. This is not an exclusion of non-torsion lifts, rational points on other surfaces, or original PointPair.

## Root classes leave only the zero root

For m=βk²,C=θ(1−m), the original matching Jacobian is

    Y²=X(X−r₁)(X−r₂),    r₁=β C(25m−9), r₂=16βC m.

Its root order is 0,r₁,r₂, so δ corresponds to the first two entries (1,β). At 17, v(β)=1, θ is a unit and v(m) is odd even for a nonintegral k. Thus v(r₁)=1+2min(0,v(m)) and v(r₂−r₁)=1+2min(0,v(m)) are odd. None of the three nonzero 2-torsion points is locally twice a point: at zero the second derivative-convention coordinate is −r₁, at r₁ the first is r₁, and at r₂ the second is r₂−r₁. Each has odd valuation. Thus rational torsion maps into the Kummer quotient exactly through the four rational 2-torsion images. The origin fails δ because β nonsquare. The r₁ root cannot work (first entry odd at 17). At r₂ its second coordinate [r₂−r₁]=[βθ] cannot equal β, since θ is nonsquare. At zero the entries are [r₁r₂]=[β(25m−9)], [−r₁]. Hence it succeeds exactly when [β(25m−9)]=1 and [C]=[−β].

## Two quadrics and the isogeny

Set u=1/(βk). The two conditions just obtained equivalently say

    1−βu²=θ z²,        25−9βu²=y₀².

Indeed −C/β=θ(m−1)/β=θk²(1−βu²), and β(25m−9)=(βk)²(25−9βu²). These equations imply a point on X(X−9N)(X−25N) at X=9β²θu² with ordered full triple (θ,−β,−N). The other two factors are −9βθ²z² and −N y₀². Conversely a non-root point of this full class recovers the very same quadrics by extracting u. Exceptional roots or infinity are not invoked.

Set x′=4X−100N, y′=8Y. This is an isomorphism to

    A′_N : y′²=x′(x′+64N)(x′+100N).

The three entries now have classes (−N,−β,θ). Translation by the rational root (−100N,0), whose entries are (−N,−N,1), changes this to (1,θ,θ), since the split Kummer map is a homomorphism. The dual pair here is the standard degree-two isogeny φ:A_N→A′_N with kernel (0,0); a rational point on A′_N lies in φ(A_N(Q)) precisely when its first Kummer coordinate is square. For affine nonroot points the formulas

    x′=x−82N+81N²/x = (y/x)²,
    x′+64N=(x−9N)²/x,       x′+100N=(x+9N)²/x

show that the desired image class is precisely (1,θ,θ) for a source point with [x]=[θ]. One can see the converse without assuming surjectivity of any Kummer map: given x′ a nonzero square on A′_N, solving x²−(x′+82N)x+81N²=0 has discriminant (x′+64N)(x′+100N)=y′²/x′, a square. Either root x is nonzero; choosing y=±x√x′ gives a point on A_N. The other two identities imply [x]=[θ]. The finitely many branch values do not weaken the existential assertion. In the forward direction all three specified full classes of the two intermediate curves are incompatible with the root images on A′_N when the first is square and the second θ≠1 (at 0 the root derivative is square but second [64N]=[N]≠θ). Conversely a rational point on A_N with [x]=θ is non-torsion by the prior ramified-good 17-adic reduction argument; taking odd multiples preserves [x] and avoids every finite boundary, zero denominator or singular slope during the two reversed maps.

At the previously studied fixed prepared β=17, θ=409, the known A_N point x=118201/81 gives u=45/373, k=373/765. The exact check finds √(−C/β)=6544/765 and √(β(25m−9))=356/9, so indeed this Hₖ can be globally lifted using the zero-root Kummer image. The calculation contrasts the actual 80/605 obstruction with a verified positive case and does not turn 409 into an indexed pole.

Run python3 -B verify.py, compare REPLAY.json. Preceding source packets: generic inversion efc41917bf9adf47c0bf136e0ba4955b943585b91b324b6007a51ba5d24547e7, fixed matching cover 2cb4d1c273daaa07469f21fbf775de086bfeac3a91fff4e177f6d3a0b6b1b393, Jacobian identification 21558846df920d4835256eb80946d44f999e7827f14aadc9ee1cb0c1edc5a1ba. Mathematical source and exact arithmetic, not Lean.
