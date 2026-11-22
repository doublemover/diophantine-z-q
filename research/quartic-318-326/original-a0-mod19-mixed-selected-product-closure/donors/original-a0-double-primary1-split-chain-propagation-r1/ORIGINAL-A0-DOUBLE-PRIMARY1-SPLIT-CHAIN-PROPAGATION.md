# Anti-constancy propagates along the split chain at one generic cancellation curve

Keep the exact input-zero double-primary intersection and one of the previously chosen actual cancellation components C′ after making the permitted finite extension of constants at 19. Work **at its generic point** on the transition exceptional plane, away from the finite common zeros of the two folds. Denote its residual function field by K_C. This paper concerns the adjacent split components in the exact depth-e model at this point, not closed points of C′, common zeros, other intersections, or the full coherent map.

## 1. The exact depth-e base and its two nodes upstairs

The regular local base at this generic point has dimension two and parameters π=19, ℓ. The already pinned exact folded functions are

    c = π^e/ℓ,       δ = 1−β(π^e/ℓ)²,       e = v₁₉(κ) > 0,

where the actual β is a 19-unit. Blow up the closed point and follow the chain ℓ_i=ℓ/π^i=0 for i=0,…,e−1, with ℓ₀=ℓ. Each step of this sequence is an ordinary blowup at a regular point. In the complementary chart to ℓ_{i+1}=ℓ_i/π, put x=ℓ_i and y=π/ℓ_i. There

    π=xy,                  π^e/ℓ = x^(e−i−1) y^(e−i).

The node joining the previous and new vertical components is x=y=0. The displayed monomial always vanishes at this node, including for i=e−1, when it is y. Thus the finite normalization in √δ is étale at the node; on the geometric special fibre there are exactly two lifts, already K_C-rational, with reduction of D=√δ equal to +1 or −1. The letter D denotes this cover coordinate here, not the slope clearing.

For every intermediate depth i<e, on the open of the i-th exceptional projective line with ℓ_i a unit the residual square equation is D²=1. Hence its normalization has two rational components over K_C, with the labels + and −. At an intermediate node the same function D is regular near both branches and selects the **same** sign on either side. There is no sign swap induced by an unrelated choice of square root.

At the last depth write L=ℓ_e. On that balanced chart the alternate cover coordinate Y=L D gives

    Y²=L²−β.

Its special component is a single rational conic over K_C, with exactly two points at infinity. At the final node chart y=1/L, and D=Y/L is regular with equation D²=1−β y². Hence the two normalized final nodes are precisely the two infinity points Y/L=±1 on the conic. Each is attached to the intermediate sign it names, when e>1. If e=1 there are no intermediate exceptional pairs. These finite descriptions over K_C give sections dominating C′ after spreading out on a nonempty open of C′; closed points of the closures are not used.

## 2. The local normalized model is regular and retains those intersections

The blowup sequence has the standard normal-crossing nodes just computed. Away from them and the centres already blown up, the even pole of δ along ℓ=0 is removed by the square denominator; on the balanced chart the actual branch sections are L=±√β after at most an unramified constant extension. They are disjoint, simple and away from the final node at infinity, and L=0 is not a branch point. At all intermediate special components away from the required sections, the stripped radicand is a unit and their normalization is étale. This also holds at each computed node by the chart above. On the balanced chart the equation Y²=L²−β is regular at its special points: the derivative in Y or in L is a unit, since residue characteristic is odd and β is nonzero. Its infinity chart is already regular by the étale node calculation. These charts cover the exceptional fibre over the indicated local centre, and show the normalized model is regular there. Equivalently one may restrict to a neighbourhood of that fibre; this makes no assertion about other centres of the global model.

The model is proper over the original local base (point blowups followed by finite normalization over an excellent ring). Properness of the good elliptic target implies a hypothetical rational coherent map to it is defined at every codimension-one point of this regular surface. [Stacks, Lemma 54.4.3](https://stacks.math.columbia.edu/tag/0C5H) resolves any remaining indeterminacy by a sequence of blowups at closed points on the regular local model. This does not change the needed values at nodes: over any old centre, the reduced geometric fibre of these point blowups is connected and consists of rational curves, so every morphism from it into the elliptic fibre is constant, including over inseparable residue extensions. Thus the closed graph projection has zero-dimensional fibres. It is proper, quasi-finite and birational over the normal surface, hence finite and an isomorphism. The map consequently extends as a morphism on this regular local model itself. In particular its restriction has a single value at each of the normalized nodes. This is not an assumption that two unrelated divisorial residues of a rational map must agree without a common regular model.

## 3. Propagation from the balanced fixed component

The generic deck involution extends to the finite normalization of these base blowups. On the balanced component it fixes K_C and sends Y to −Y. Any restriction of the hypothetical map to the balanced conic is constant **over K_C**, since the conic is rational and an elliptic curve admits no nonconstant map from P¹. The anti-equivariance then makes that common value a target 2-torsion point. All the actual targets E_m here have their full 2-torsion over the finite field of constants at 19 (their roots 0,m,−3m are distinct), so this value is constant even as C′ varies. This uses the same fixed-divisor anti-action already established separately.

Each intermediate split projective line also has a constant elliptic value over K_C; by itself that point might vary with C′. The morphism property and the K_C-rational attachment at the final node force its two adjacent sign values to equal the same balanced value. Working backwards, every sign-labelled intermediate component is attached to the next one at a K_C-rational node, and so has the same restriction. This kills all possible nonconstant anti-image on **this exact adjacent split chain** above the generic simple-cancellation curve, independently of whether Jac(C′) has an ordinary elliptic factor. The involution may exchange the intermediate components; their equal values follow from the two attachments, not from treating them as invariant individually.

If a proper graph retains any of these divisorial valuations, the specialization is the same by properness/uniqueness; contracting one cannot make its recorded value nonconstant. The argument does not constrain a new valuation centered at a closed point of C′, a common zero of f_±, another singular branch chart, or an isolated Ready index. It says neither that a global anti-map is impossible nor that an elliptic quotient of the high-genus base exists.

Exact sources: double-primary and balanced generic chart list 5a8a5a55f694f97b8d2eff9ab4e7f90eb6104437fb9a62125b7546675ea9022b / paper 17703e3d5a307e78829b7fb017fcef93d4396511a0a40b8b675397bf74fafcae; balanced deck list 1bfcfe502dbfbf21a04b1a466ae742399de97fae0bc27c3ca4caa66e83f09f48 / paper 9033df877acdfe11f20ecd76510b442362a88587e25a6791b24f4904fbbdbde9; isolated regular-depth donor list 02046fb7d8068bab9d564039451c0c75db471d899651cce916455681cdd8f15c. This is chart algebra and a map-descent argument only, with no arithmetic search, build or remote action.
