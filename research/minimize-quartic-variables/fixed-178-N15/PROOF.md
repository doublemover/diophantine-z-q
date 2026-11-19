# A three-contact weighted abscissa sum: fixed N=15, 178 total rational variables

Let f be the explicit signed integer polynomial printed in quartic178-N15.txt
(SHA-256 2dbf9ae700ad51104ddd8cd9af3d1436fb768f17c3def61cf834fffe0769a96f).
Conditionally on the arithmetic inputs of the compact fixed180 donor and with precisely its five-contact height constants, for each X in Q:
    
    X in Z  iff  there exist 177 rational witnesses with f(X, witnesses)=0.

The count includes X. This is not the old 180 polynomial, an unconditional result, a claim of minimality, or a formal proof checked by Lean.

## A changed pair of measured identities, not an elimination on old fibers

Use the compact180 stored-coordinate numbering until the final dense renumbering. In the order of donor rows, write the two pairs (78,137) and (138,139) as A_c+Y_c=0 and U_c−z²Y_c=0 (Y₀=x164,Y₁=x165; x60=z², x37=z=X²+48). Each pair becomes the single quadratic A_c+U_c=0, with no Y. Every other residual is unchanged except for the cosmetic renumbering. This is NOT the old elimination z²A_c+U_c=0. The source component decomposition in donor/donor180/inverse.py and the fixed-180 gauge show that the coefficient of the old Y was the same as the coefficient of the OTHER role contributions: the old Y contributed exactly the relevant component of x(Q₁) to the displayed shifts, so U contributes z² times this component. There is no change to the signed input z, either sign of its mark, any root multiplier at the scalar, any pole widget, any finite-pair chart, q=u₀+u₁+u₂−3 or its inverse guard, any contact rational function, or x60=z². Concretely put

    S₀ + ρ S₁ = z² x(Q₁) + x(Q₂) + x(Q₃) + x(Q₄),   ρ²=2.

Rational vanishing yields the two measured identities t₁−t₀=13+S₀/2 and t₂−t₁=17+(S₀−S₁)/2. The unchanged rows recover the same four genuine finite elliptic points and all their labels as before. We cannot quote the donor's UNWEIGHTED full-field height theorem verbatim to these shifts. The following explicit extension is the essential new ingredient.

## Effective moving-weight bound, including denominator primes, zero indices and torsion translates

Write z=A/D in lowest terms, D>0; z≥48 so A>0 and h(z)=log max(A,D). Let w=(A²,D²,D²,D²); all w_i are positive integers. In K=Q(√2), d=3−√2, set Z_w=Σ w_i x(Q_i)+(A²+3D²)d+1. Let m_i be the signed multiples in Q_i=[m_i]R₀+T_i, M=max(1,|m_i|), and B=max(1,|m₁|/2,|m₂|,|m₃|,|2m₄+1|). The fixed input normalized curve and torsion are exactly those of donor/donor180/arithmetic/FULL-FIELD-HEIGHT.tex. We prove

    max_i h(x(Q_i)) ≤ h(Z_w) + 24 log M + log864 + h(d) + 16 h(z).

At each finite place, select exactly the donor's deep subgroup. Its principal-part lemma gives x(Q_j)=(m_j L)^−2+integral with a common L at that place, whenever j is deep; a deep nonzero point cannot have m_j=0. Nondeep points have integral abscissa (odd prime ramification index 1; all dyadic denominators of the formal logarithm are units). Suppose i is deep and J is the set of deep indices. The principal part of the sum is (m_i L)^−2 times C_J/∏_{j in J,j≠i}m_j² with positive nonzero integer

    C_J = Σ_{j in J} w_j ∏_{k in J,k≠j} m_k².

Every discarded term and the translation are integral, INCLUDING places dividing D or A, because integer weights were used before taking principal parts. If this leading term has a pole, its valuation exactly controls the sum; otherwise the whole local height of x(Q_i) is bounded by v(C_J). Thus local height loss is ≤v(C_J), also when the leading term is integral and the whole sum cancels. For each i at most eight subsets contain it. The ordinary absolute height normalization over K gives Σ_{v finite} weights(v) v(C_J)=log C_J. Bound C_J≤max(A,D)² |J| M^{2(|J|−1)}. Summing the eight bounds for a fixed i gives 16h(z)+24log M+log864. A nondeep ith point has zero finite local height; zero index (finite torsion) is never deep and causes no division; the sum only ranges over subsets of actual nonzero indices. Repeated and negative indices cause no problem. At both real embeddings x≥−d and w_i≥1, so Z_w≥1; if x_i≥0 then x_i≤Z_w, and otherwise |x_i|≤d. This adds at most h(d) to the total loss. This is a bound for the algebraic number over BOTH embeddings, not a rational field-trace assertion.

By the donor's normalized duplication bound h(x(Q_i))≥m_i²/4−6 at every nonzero index. Using 24log M−M²/8<43 as in its four-point corollary yields M²<8(h(Z_w)+16h(z))+456 and B²≤5M²+5. The trivially bounded case of all indices zero satisfies the same inequality. Therefore

    B² < 40 h(Z_w)+640h(z)+2285.

Eliminating S₀,S₁ from the two actual shifts now gives

    Z_w = D²[−(2+2ρ)t₀+(2+4ρ)t₁−2ρt₂−26+8ρ]+(A²+3D²)d+1.

Its coefficients are integers of K at every finite place; clearing the three rational argument denominators there costs at most the sum of their local heights. At either real embedding, the sum of the four absolute coefficient bounds, including the affine coefficient, is <100 max(A,D)² (use |ρ|<1.5, d<4.5). Hence h(Z_w)≤Σ h(t_j)+2h(z)+log100, and in particular

    B² < 40 Σ h(t_j) + 720h(z) + 2500.                              (*)

## Reverse

The 148 unaltered equations have exactly the same signed geometry and cubic scalar: C=149¹⁵, β=1−51X², and R=(557·149)C²P(β)/(P(β)−P(705024)) with P(B)=B(B−2401)(32B+343). The donor's proof establishing v₁₄₉R=31 for **all** rational X, v₁₄₉(a)>17·31/8, and the height bound does not use either aggregate. Write c_a=|a|. For X≠0 it gives 149⁶⁶|c_a, h(β)<c_a/4, and h(z)≤h(β)+log2450<c_a/2≤B/2; X=0 is integral independently. The raw pole and reference zero cases, the signed z-role on both slots, and half-integral label n are exactly those of donor/PROOF.md and its antecedents. Each of the three genuine argument radicals M_j outside the same Γ still has M_j³|Δ when the affine Lucas residual Δ is nonzero and M_j|J_X=|num(z−n)| if z≠n. Their proof only uses the chart at THAT measured argument, hence is unaffected by its changed abscissa shift. Empty radicals, the midpoint, and every allowed affine/torsion point follow the donor; zeros of the raw marked product and the guarded reciprocal q are still disallowed rather than divided through.

Here are explicit numerical allowances for (*). Since B≥149⁶⁶>10^9, 720h(z)+2500<360B+2500<B²/10000. Thus B²<(400000/9999)Σ h(t_j); the coefficient on a common bound for all three is <120.02. If Δ≠0 the donor reflected sharp bound gives h(t_j)≤log33+V with V=𝒞 sqrt(21/10)|Δ|^(1/3+1/36036)(log J_*+log|Δ|/6). Here 𝒞≥1 and log J_*>1. To avoid any reliance on how large the constants are: 120.02 log33 < B²/10000 at the stated B, so absorbing this second negligible term gives B²<121 V. This is exactly the donor's previous 121 and hence the same contradicted inequality exp[(2/3)(1−1/6006)s]<500·2³⁰⁰(53+2s/3) at s=log B≥66log149. If Δ=0 but J_X nonzero, M_j≤J_X≤4B exp h(z), the donor coarse bound h(t_j)≤K M_j(22+.5log M_j)² with K=2³⁰⁴ gives e^s<484K exp h(z)(23+(s+h(z))/2)², since 4·120.02<484. The same elementary manipulation yields s<240+c_a, inconsistent with the unchanged Lucas lower bound s≥(c_a−6)log(c_a−3)>320c_a. We conclude z=n in (1/2)Z. Since 2X²=2z−96 is integral, the square of the reduced denominator of X divides 2, hence X is integral.

## Forward

For every integer X take z=X²+48 (including 48 at zero); R, scalar H/Q₂ choices, 2,3,17 and real neighborhoods, and positive AND negative odd support preparation are EXACTLY the donor's. Fix Q₁=[z]P₀ (not [β]P₀), Q₂ a nonzero double on the required progression, and the same true affine-Lucas Q₃,Q₄. These differences are chosen before selecting slope/primes. At each real embedding x(Q₁)≥d>0 because Q₁ is a nonzero double on the identity component of y²=x(x−d)(x+d). If x(Q₁)=g₀+ρg₁, then g₀>0 and |g₁|<g₀/√2, so BOTH g₀ and g₀−g₁ are positive. The old gap lower bounds ≥7 and ≥9 are increased by (z²−1)g₀/2 and (z²−1)(g₀−g₁)/2 respectively. This proves all 30 translated finite marks stay distinct, not merely their aggregate cardinality.

Use the same fixed-data simultaneous prime theorem on THESE new rational shifts. Its hypothesis allows any finite fixed list of distinct offsets with denominators cleared by a square and the retained split/point/progression conditions. Choose D₀ and the finite exceptional set anew after fixing the points, including all pairwise offset differences, denominators, multipliers (notably z), and previously prepared primes; then use the same one common λ=u/(D₀² w²), high denominator divisibilities and slope/cutoff. The 30 resulting primes may be as large as needed with pmax≤5pmin/4, and the full 2-torsion and Hasse bound exclude every selected prime from every reduction order. Equal-depth CRT and compact real returns for the prepared reference therefore still hold simultaneously. The original q=u₀+u₁+u₂−3 uses the three new true rational harmonic values, not old witness values. It is positive at a sufficiently large real slope, and its value at each selected prime is governed by that argument alone. All cap inputs then have positive valuation one at their own ten primes, square reduced denominators, and original small-place/real preparation (limiting value (204/409)²). Invoke the unchanged prepared realization separately for all four pole widgets. Fill the other coordinates via the same genuine charts; the two new aggregate equations hold by construction. Over Q the sum of squares vanishes if and only if all 150 residuals vanish.

## Verification and premises

Run python -B build.py in this directory. It checks the compact180 donor row commitment, the two isolated slot occurrences and their coefficients, unchanged dense renumbering on all other coordinates, primitive residuals, the quadratic degree ceiling, independent integer collection into the quartic, exact agreed literal bytes, and occurrence of all 178 coordinates. The 150 residuals give 3,494 distinct monomials; maximum coefficient 365 bits, 87,020 ASCII bytes, X⁴ coefficient 1. N is 15, not a parameter to select.

The additive weighted-height estimate is proved here, not an added black box. Remaining inputs are exactly the reviewed effective v62/compact180 inputs (fixed family H4.1, actual rank-one normalized elliptic curve and point charts, formal and compact returns, prepared rational pole realization and negative-odd-pole obstruction, compatible arbitrary-fixed-data thirty-prime progression with its quantitative cutoff, the full-field local principal-part and normalized duplication estimates, and affine Lucas growth). No ordinary abc assumption or ineffective weighted-trace corollary is added. Original Brox source: José Brox, diophantine-z-q_improvements commit d3a8c223, CC BY 4.0 (license in donor/donor180/donor165/V74-LICENSE.txt). The weighted change is ours, not a claim by the donor.
