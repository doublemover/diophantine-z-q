# Direct signed optimal embeddings on the actual 416 marked orders

There is a genuine second exact finite computation of the oriented genus-fiber ranks in 29ca682d…. It counts **primitive optimal embeddings** in the fixed quaternion orders directly, with an explicit genus sign, rather than computing class-field polynomials or replaying characteristic-zero translates. For m=455,d=323 the entire pair of 416-label multiplicity counters is identical to the prior 5,760-point replay. It is not a better-complexity algorithm for production: its direct weighted norm is md², not the ST norms 37d and 35md.

## Exact oriented domain

Let p=53, K=Q(sqrt(−m)), with the exact preceding compatibility hypotheses: m≡23 mod24, d≡11 mod24, both squarefree, prime-to one another and 2·3·53, and every prime of d split in K, with p inert. Write B=B_{p,∞}, and take the fixed Eichler order R of level 48. It is the same geometric marked curve model X=B×\ B̂× /R̂× used before. Let g_x be representatives of its 416 marked labels, so R_x=B∩g_x R̂ g_x⁻¹ is each actual left order. Keep a single base b and field embedding ι:K→B from the previously fixed low point of conductor d and this marked orbit.

Use [Cornut–Jetchev, Theorem 3.1, Corollary 3.2 and Remark 1 after §3.6, and §§4.8–4.10/Corollary 4.1](https://webusers.imj-prg.fr/~christophe.cornut/papers/liftings.pdf). Their oriented version keeps the residue-field isomorphism at the inert division prime; the statement with conjugate pairs just suppresses that choice. Here d is prime to the level and to p. On the subset with the actual two level signs at 2 and 3 and the actual residue orientation at 53, the marked points reducing to x correspond to the corresponding R_x^×-conjugacy classes of optimal embeddings O_d→R_x. In particular no averaging over the opposite orientations is allowed.

For specificity this subset is exactly one Pic(O_d)-torsor. In the adelic description its defining condition at each ℓ is that the local conjugating element belongs to the same ι(K_ℓ)^×–R_ℓ^× double coset as b_ℓ. At primes away from 2,3,53,d the optimal lattice is a fractional ideal of the maximal order, unique up to K_ℓ^×; at a split prime with d∤ℓ it is the direct sum of its two projections. At ℓ|d the order is the congruence order of conductor ℓ in Q_ℓ×Q_ℓ. Indeed scale the projections of the lattice to Z_ℓ by diagonal elements of K_ℓ^×. A sublattice with surjective projections is the graph of an isomorphism between their cyclic quotients by ℓ^e, hence has the form y≡u x mod ℓ^e with u a unit, after the same projections. Its multiplier ring has conductor ℓ^e; optimalness forces e=1, and diagonal units can make u=1. At 2 and 3 the order is maximal split, and the selected one of the two eigenlines specifies the cyclic-level orientation; at 53 the two division lattice classes are the parity classes of a division uniformizer, distinguished by conjugation on F_{53²}. With those fixed local double cosets, the global set is K×\K̂× /Ô_d×, by the stabilizer equality at the optimal base. This is the same orientation and Artin action as in the true marked CM reduction, not an arbitrary assignment to quaternion orders.

## A genus sign recovered directly from the optimal embedding

Put Ψ=χ_{−d}, regarded as a character of the ideles of Q trivial on Q×, and keep χ=Ψ∘Nm_{K/Q}. Let ξ=d sqrt(−m)∈O_d, and for each ℓ|d use one fixed identification R_ℓ=M₂(Z_ℓ), which exists as ℓ∤48p. In the coordinates of R, the transported ξ in any candidate is integral. Since ξ²=−md², its reduction is nilpotent. It is nonzero: if ξ were in ℓR_ℓ, ξ/ℓ and 1 would generate the full local maximal order inside the embedding (ℓ odd and d/ℓ a unit), contradicting optimal conductor ℓ. Thus the reduction U is a rank-one nilpotent on F_ℓ².

Define an exact local sign
```
η_ℓ(U) = ( det(v,Uv) / ℓ ),    v∉ker U .
```
This is independent of v: in a basis (e,f) with Ue=0 and Uf=c e, det(v,Uv)=−c·(f-coordinate of v)²·det(e,f). For k∈GL₂(F_ℓ),
```
η_ℓ(kUk⁻¹) = (det k / ℓ) η_ℓ(U).
```
Thus this sign refines the ordinary GL₂ local conjugacy class. For example, a nonzero nilpotent with a single above-diagonal entry is GL₂-conjugate to its multiple by a nonsquare, which has the opposite η. The usual (unsigned) optimal embedding mass loses this datum.

For the point a·b, choose γ∈B× and k∈R̂× with ι(a)b=γ g_x k. In the fixed R-frames put
```
ξ_0=b⁻¹ι(ξ)b,  ξ_x=g_x⁻¹γ⁻¹ι(ξ)γg_x,  ξ_x=k ξ_0 k⁻¹.
```
The last equality follows because ι(a) commutes with ξ. Taking reduced norms in the first equation and applying Ψ gives exactly
```
χ(a) = Ψ(nrd(g_x)) / Ψ(nrd(b))
       · ∏_{ℓ|d} η_ℓ(bar ξ_x) / η_ℓ(bar ξ_0).
```
The rational factor nrd(γ) disappears by the global product, and at infinity the reduced norm is positive. At primes not dividing d the character is unramified, so all components of nrd(k) there are invisible; at ℓ|d its restriction to units is the Legendre character. This also shows independence from a gauge change g_x→βg_xk' (β rational): its norm factor is exactly compensated by the transformed η, in addition to the common base normalization. Taking the inverse Artin convention does not alter the quadratic character.

This is a direct finite read for the exact genus weight of an optimal vector in the marked order. If only the squared detector or the test “nonzero” is needed, the one constant base sign may be dropped; for the actual ordered genus-half counts it is fixed by the chosen base. A formula merely counting embeddings up to unrestricted local GL₂-conjugacy cannot recover the sign as a class function of that quotient. In particular the standard global mass in [Voight, §30.4, Theorem 30.4.7](https://jvoight.github.io/quat-book.pdf) supplies unweighted multiplicities summed across orders and does not implement this signed phase and its label-dependent contraction. This is not an impossibility theorem for a genuine signed relative trace identity.

## Exact bounded replay with both p53 orientations distinguished

An embedding is determined by the image of Ω_d=(1+ξ)/2. Equivalently in R_x/Z take a quotient vector of exact discriminant −md², with odd trace of any representative, and reconstruct Ω_d by its integral scalar adjustment. Primitivity/optimalness reduces to ξ not divisible by ℓ in R_x at each ℓ|d: a larger order can only have index a divisor of d, since m is the squarefree fundamental part and gcd(m,d)=1. The division condition picks the orientation at p. At 2 and 3 it suffices to demand that Ω_d have its prescribed eigenvalue on the literal C16 and C3 line. These are restrictions in actual fixed geometric Tate frames, not arbitrary character filters.

The checker uses the exact maximal-order quotient lattices and the common basis (1,ω,γ,ωγ) of the prior q29 book. It uses the same Eisenstein sieve only for the unweighted exhaustive norm shell, then uses the new principled character (above), entirely different from the earlier ST Type-I/II weights. At 17 and 19 choose any one fixed split matrix frame for this quaternion basis; the exact matrix identities for ω, F, and γ=(F−1)(1+2ω)⁻¹ are checked. All target orders were transported from the base by q29 arrows, so at these primes we may use the same frame; the two other change-of-frame places 2 and 3 have determinant-one marked adapters before using this norm factor. We can choose the norm idele of g_x to be q29 (or its inverse, irrelevant to a quadratic character) at the transport place and 1 elsewhere. For d=323, (−323/29)=+1, so this factor is 1 on all five classes. No assumption of a trivial norm gauge at arbitrary d is made.

The fixed reference dβ≡1 mod96 makes the eigenvalue of Ω_d equal to 1 at both 16 and 3. The scalar adjustment comes from the actual HNF integral representative; division by 2 is in Z before reducing modulo 16. At p the two allowed residue orientations give coefficient ±8 of ω in the reduction of that representative, since (1+2ω)²=−3 and 3·8²≡md² mod53. No arbitrary counting factor is divided away at j=0: choose the actual one marked representative among the three automorphic mark pairs, as already pinned in the 32-row table. The stabilizer of a C16,C3 mark is ±1, which acts trivially on embeddings; for the other four j's there is no effective automorphism group from the start. Each eligible vector for the chosen orientation is counted once in its actual genus half.

At m=455,d=323, the exact shell norm is 47,469,695. The counts on the five maximal orders for each 53 orientation separately are 446,1325,1325,1328,1336, summing to 5,760. Both genus halves have 2,880 labels with multiplicity. The two full marked multiplicity counters for **phase +8**, with **no half swap**, match the prior independently formed actual 5,760-point Gauss/isogeny replay at all 416 addresses. The injective comparison orders the signs as (−,+); each table's complete sorted count list is fingerprinted in the JSON. Phase −8 gives the same signed residue 11 in this example but does **not** give the same two marked counters. This certifies that matching the scalar alone would not have verified the orientation. The direct path took about 1.2 seconds locally and does not evaluate a characteristic-zero class field. It is an independent finite read of the same result, not a new curve or production conductor.

Replay with both exact donor JSONs (and adjacent existing Eisenstein sieve):
```sh
python3 -B replay_direct_signed_embeddings.py \
  /path/to/ACTUAL-ODD2544-MARKED-ORDERS-Q29.json \
  /path/to/ACTUAL-FULL-TRACE-F53.json \
  | cmp - EXACT-DIRECT-OPTIMAL-EMBEDDING-REPLAY-323.json
```

## Exact complexity boundary

For fixed old conductor r, K and moving split q, d=rq. In this direct read there are exactly h(O_r)(q−1) oriented optimal embeddings across the marked orders, counted with the true multiplicities, before any cancellation. An explicit embedding enumeration thus has Ω(q) output steps. Even its primitive ternary norm has size md², so the literal Eisenstein coordinate scan is on d√m scale, whereas the two existing coefficient shells at norms 37d and 35md are on √d and √(md) scales. Therefore this is a genuine dual *exact finite check* and a cleaner characterization of the missing signed Brandt trace, not a quicker method on the prime ray or a computation for the actual large scalar. A successful compressed trace must contract the marked signed embedding counts without generating the embeddings or passing to the unsigned local mass.
