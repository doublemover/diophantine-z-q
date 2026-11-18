# Opposite explicit Cassels–Tate pairings on the two actual ray-contact covers

Use the *same* prepared squareclasses β,θ as the realization and the earlier paired genus computation. The theorem needs positive coprime squarefree β,θ, β≡17 mod24, θ≡1 mod24, all p|β congruent to 1 mod4, and a primitive nonzero θ-conic

    ℓ² − βa² = θe²,       ℓ>0,    gcd(ℓ,βθ)=1.

In particular (θ/p)=1 for p|β and (β/q)=1 for odd q|θ (if q|a or q|ℓ the primitive equation and squarefreeness contradict the stated assumptions). Also e is a unit at each p|β. In the three actually ray-prepared contact rows β=17 times five distinct primes ≡1 mod408, and ℓ is the denominator of the *same* prepared square factor z/17=a/ℓ in lowest terms. The existing preparation yields exactly this θ-conic. This is not an assertion about a scalar marker with 3-mod-4 prime factors.

For k=2^h or 3·2^h (any h≥2), including 4 or 12, let m=βk² and

    r₁=βθ(1−m)(25m−9),       r₂=16βθ(1−m)m,
    J_k: y²=x(x−r₁)(x−r₂),       r₂−r₁=9βθ(1−m)².

These roots are distinct. Use ordered roots 0,r₁,r₂, defining the 2-Kummer classes δ=(1,β,β), ε=(β,1,β), with the convention x−root_i=class_i times a square. Denote by ⟨δ,ε⟩_k the multiplicative sign of the explicit 2-Selmer Cassels pairing (−1 represents 1/2), hence of the images in the actual elliptic Cassels–Tate pairing. For the identification use the classical split-root 2-Selmer tangent formula, cf. [Shukla, §3.1.1 and Theorem 3.3.7](https://epub.uni-bayreuth.de/id/eprint/8348/1/thesis.pdf), or the earlier reviewed explicit Sel₂ pairing package. Then

    ⟨δ,ε⟩_(3·2^h) = (ℓ/β) = ∏_(p|β) (θ/p)₄,
    ⟨δ,ε⟩_(2^h)  = −(ℓ/β).

Thus on EVERY eligible actual contact, one (and only one) of these particular pairings is nonzero, regardless of the unknown value of the bit. The associated J_k has an explicit nondegenerate (Z/2)² in Sha(J_k)[2]: the two classes are independent by nonzero pairing and alternation for an elliptic curve. This subgroup splits off in Sha[2∞] as an abstract group, with no global finiteness assumption: restriction of pairing to its nondegenerate finite subgroup gives a retraction by the identification with its character dual. The class δ has no rational representative in its 2-cover and neither marked Selmer element is in the image of Sel₄. For the other parameter the single value +1 says neither global solubility nor absence of Sha. Applying these statements to a named realization H_k uses its separately established identification with the δ torsor; no absolute assertion that every original realization route is obstructed follows.

**Both classes genuinely belong to Sel₂.** At real, at 2, and anywhere β is a local square both are trivial. Outside 2,3 and β, the only possible odd bad primes divide θ, 1−m, 25m−9, or k. At each such odd prime other than 3, β is a square: for θ by the preparation, for 1−m or 25m−9 it is (1/k)² or (3/(5k))² in the residue field and Hensel applies (5 cannot divide 25m−9); k has no prime factor outside 2,3. At odd good reduction the unit-valued Kummer slots are unramified and the local Kummer image is the full unramified subgroup. Here one may see equality by the usual good-reduction Kummer sequence, or that the unramified subgroup has order four (all 2-torsion rational) and so does J_k(Q_p)/2.

At p|β, set g²=θ and h²=1−m in Q_p. For δ take the lift t=1,x₃=0,x₂=3g(1−m),x₁=4βkgh of the r₂ root to the δ cover. Its equations are x₁²−βx₂²=r₁t², x₁²−βx₃²=r₂t². For ε the r₁ torsion point has Kummer coordinates r₁ and r₁(r₁−r₂), of squareclasses β and 1 since −1 and θ are squares there.

At 3, when v₃(k)=1 all r_j are divisible by 9, with r₁/9=2 and r₂/9=1 modulo 3. Scaling x by 9 and y by 27 gives good reduction. Both classes have unit slots. When v₃(k)=0, both r_j≡2 mod3 and (r₁−r₂)/9≡1 mod3. For δ take x=1: x, x−r₁,x−r₂ have squareclasses 1,β,β. For ε take x=r₁+9: x−r₁=9 and (x−r₂)/9≡2, giving β,1,β. In each case the product of three slots is square, so the point exists.

**Rational tangents.** In Q(√β), write

    A+B√β = √β · (ℓ+a√β)/e · (1+k√β) · (3+5k√β).

Its norm is (−β)θ(1−m)(9−25m)=r₁. The conic omitting x₁ has tangent L₁=x₂−x₃ at (x₂,x₃,t)=(1,1,0). The conic omitting x₃ has tangent L₃=A x₁−β B x₂−r₁t at (A,B,1). These cover the two nontrivial ε slots; globally constant rational tangent factors do not affect the product by reciprocity. The desired value is ∏_v(L₁L₃,β)_v on any δ-local points avoiding tangent zeros.

**At β.** Take the explicit δ lift above with g≡−ℓ/e modulo p. Put a₀=ℓ/e, a₁=a/e. Since
A=β[a₁(3+5m)+8ka₀], B=a₀(3+5m)+8βka₁,
we get x₁ divisible by β, x₂≡−3a₀, and L₃/β≡18θ mod p. Thus v_p(L₁L₃)=1, (L₁L₃)/β≡−54a₀θ. The Hilbert symbol is (6a₀/p): here (β,β)_p=(−1/p)=1, θ is a square and p≡1 mod4. Multiplying over β gives −(ℓ/β). Indeed (6/β)=−1 since β≡17 mod24, whereas (e/β)=1: for odd q|e, q∤β and ℓ²≡βa² mod q gives (β/q)=1, with both coordinates units by primitivity and squarefreeness. The sign and factor 2 in e contribute + by β>0, β≡1 mod8 and the individual p≡1 mod4. Reciprocity gives the assertion.

**At 3.** β is an unramified nonsquare unit, so the local sign equals (−1)^v₃(L₁L₃). When v₃(k)=1, A'=A/3 and B'=B/3 are integral at 3: the unramified quadratic norm of A'+B'√β is the unit r₁/9 and {1,√β} is an integral basis locally. Take t=1,x₃'=0 after x_i=3x_i'. Independently choose the two signs of x₁'²=r₂/9 and x₂'²=(r₂−r₁)/(9β), both unit squares. The four reductions (±1,±1) give points on x₁'²−βx₂'²=(r₁/9)t². The reduced conic is smooth; at most one pair is the tangency point (A',B',1), so choose another. Then L₁/3 is a unit, L₃/9 is a unit, giving sign −1. When v₃(k)=0 the norm A²−βB²=r₁ is a unit; A,B are integral by the same argument. Above x=1 choose x₁,x₂ with either sign and x₃ opposite x₂ mod3 (both are unit roots). The same tangent avoidance on the smooth H₃ reduction gives L₃ a unit, L₁ already a unit, hence sign +1.

**All remaining places.** The square-β places give +1. At any remaining odd q≠3 of good reduction with β a nonsquare, r₁,r₂,r₂−r₁ are units and A,B integral by the unramified norm. Choose a projectively primitive integral δ point avoiding exact zeros. Reduction is nonzero on each relevant conic (else the other cover equation forces the omitted coordinate to vanish). If L₁ vanishes modulo q, then t=0 mod q and x₂+x₃ is a unit, so L₁ has even valuation by (x₂−x₃)(x₂+x₃)=9θ(1−m)²t². If L₃ vanishes modulo q the conic point is its tangent point, t a unit, and

    L₃(Ax₁−βBx₂+r₁t)=β(Bx₁−Ax₂)².

The other factor is a unit, again giving even valuation. This proves the claimed product. Finally the equality (ℓ/β)=∏(θ/p)₄ follows from the *same* conic modulo each p: (ℓ/p)=(θ/p)₄(e/p), and the product of the latter factors is 1 as above. The independently verified relative 8-rank comparison for the two original support Heegner fields is ε(γθ)/ε(γ)=(ℓ/β) with the identical denominator and sign convention (ε=+1 for 8-rank one). Thus these signs link the realization's actual cohomological obstruction to the relative 8-rank, not to either absolute class number or the rank of the original E_n. No Lean elaboration.

**Infinite geometric consequence.** The bit is independent of h, so one entire half of the listed slopes gives nonzero pairings. Within that half the cross ratios λ=r₁/r₂=(25m−9)/(16m) are pairwise distinct as m grows. Since j=256(1−λ+λ²)³/[λ²(1−λ)²] is a nonconstant rational function of λ, these curves represent infinitely many distinct geometric isomorphism classes. The rooted-quartic isomorphism and Galois translation computation of the companion applies for arbitrary such k (m>9), so the actual H_k giving these classes are locally soluble with no global point. This says nothing about slopes outside this subfamily or the solubility of a different realization.
