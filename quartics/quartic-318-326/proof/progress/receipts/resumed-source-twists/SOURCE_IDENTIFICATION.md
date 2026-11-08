# Recovering the arithmetic Kummer twists from the published Jacobians

Status: author geometric argument awaiting independent review. Exact arithmetic and the conditional algebraic field-equivalence package have passed kernel replay and a recursive audit of all 90 declarations in four modules. This note does not construct a PEL moduli object or a PEL comparison map in Lean.

## Fixed sources and historical scope

The adopted manuscript is `diophantine-z-q/manuscripts/quartic_v10.tex`, SHA256 `9559b22cc581346da1b3150fa9b8dfb62cfb048f6aac0b866448ae7ae879ff38`. Its paragraphs beginning “Recovering the contact line from published quotients” establish the labelled branch data used below. Its existing check `degree8-original/arithmetic/geometry/check_published_quotients.py` already records both Tables 2 and 3, but compares their j-invariants and recovers branch cross ratios; it does not implement the twist-recovery argument below. This is an added connection between existing arithmetic inputs, not a claim that the manuscript's branch proof was absent or newly repaired. The manuscript has not been edited.

Primary source: J. González and V. Rotger, *Non-elliptic Shimura curves of genus one*, JMSJ 58 (2006), 927–948, Theorem 4.2 on p.938 and Tables 2–3 on p.939, DOI https://doi.org/10.2969/jmsj/1179759530. The existing PDF `fiber-field-bridge/gonzalez-rotger-2006.pdf` has SHA256 `e595d1a428f20e1c6b3695bc37be658ca12c517fb6600171f531fe931b796c3a`. Its p.939 was freshly rendered and visually inspected in `GR2006-page939.png`. The sentence beneath Table 3 explicitly identifies E=Jac(X_D^(m)) with y²=x³+Ax+B. Thus those entries specify arithmetic elliptic curves, not merely j-invariants.

## Precise geometric inputs

Let X be the geometrically connected smooth proper maximal-level discriminant-210 Shimura curve over Q. Retain the already established faithful, Q-defined action W≅(Z/2)^4, quotient coordinate t=32s, and the five rational branch points with distinct inertia generators:

- a₀=0, label e₀=w₁₀₅;
- a₁=32, label e₁=w₇₀;
- a₂=76832, label e₂=w₄₂;
- a₃=−343, label e₃=w₃₀;
- infinity, label e∞=e₀+e₁+e₂+e₃=w₂₁₀.

The four finite labels form a basis, every inertia group has order two, and there is no other branch point. The published theorem identifies the genus-one curves Cᵢ=X/<eᵢ> with its four Table 2 rows, and Table 3 gives their Jacobians. All quotients in this note are over Q. The t-coordinate is not the modular j-coordinate.

## Kummer form, without guessing constants

The dual character χᵢ:W→{±1} that is nontrivial on eᵢ and trivial on the other finite labels has a quadratic fixed-field extension of Q(t), branched only at aᵢ and infinity. A characteristic-zero quadratic extension of Q(t) with exactly this branch set is Q(t)(√(cᵢ(t−aᵢ))) for some cᵢ∈Q×, unique modulo Q×². Indeed, write the extension by a square root of a rational function. Its divisor has odd valuation exactly at aᵢ and infinity. Removing (t−aᵢ) leaves even valuation at every irreducible polynomial, hence a constant times a square in Q(t).

The four dual characters span the character group. Consequently the full field Q(X) is their compositum, and is isomorphic over Q(t), with the labelled W action, to the four-root field with these as-yet-undetermined constants. This uses the actual W-extension, not merely a curve with the same genus or branch cardinality.

## Why the four published Jacobians determine the complementary products

Fix i. The residual group W/<eᵢ> acts faithfully on the genus-one curve Cᵢ, and has order eight and exponent two. Over an algebraic closure choose an origin. Its map to automorphisms of the Jacobian has image {±1}: an exponent-two subgroup of the origin-fixing automorphism group has at most two elements, whereas the translation subgroup has at most four elements. Therefore the translation kernel has order four and is the full Eᵢ[2]. These assertions are independent of the chosen geometric origin. Because the residual automorphisms are Q-defined, the translation action and its quotient are Q-defined.

Every eⱼ with j≠i has a fixed point on Cᵢ, descended from its fixed points on X, and is nontrivial on Cᵢ. Thus it is not a nonidentity translation, and acts by −1 on the Jacobian. The sign character of the residual action is consequently the sum of the other three dual characters χⱼ. Its fixed field is

    Q(t)(√(Cᵢ ∏_{j≠i}(t−aⱼ))),  where Cᵢ=∏_{j≠i}cⱼ.

Call the corresponding genus-one quotient Dᵢ. It is Cᵢ/Eᵢ[2]. The induced degree-four isogeny of Jacobians has kernel Eᵢ[2], so the factorization of multiplication by two gives Jac(Dᵢ)≅Eᵢ over Q. This is an arithmetic isomorphism, not only equality of j-invariants or an unspecified isogeny. Since the displayed double cover has odd cubic degree, its smooth completion has a Q-rational point at infinity. Hence Dᵢ, with that point as origin, is itself its Jacobian.

## Exact coefficient calculation

Write Pᵢ(t)=∏_{j≠i}(t−aⱼ). After t=x+(sum_{j≠i}aⱼ)/3, write Pᵢ=x³+Aᵢx+Bᵢ. In i order 0,1,2,3, the pairs (Aᵢ,Bᵢ) are:

- (−1975726875, −33798988093750);
- (−5929627249/3, −913149747428114/27);
- (−129649/3, 90882286/27);
- (−5900698624/3, −906535659044864/27).

The corresponding published pairs are, in label order 105,70,42,30:

- (−1053721/3, −2163135238/27);
- (−50401/3, −22628702/27);
- (−129649/3, −90882286/27);
- (−5762401/3, −27665272798/27).

Direct rational equalities are A_pub=dᵢ²Aᵢ and B_pub=dᵢ³Bᵢ, where

    d=(1/75, 1/343, −1, 1/32).

All Aᵢ and Bᵢ are nonzero, and all four discriminants are nonzero. The curve y²=CᵢPᵢ(t) has short-Weierstrass coefficients (Cᵢ²Aᵢ,Cᵢ³Bᵢ), by x'=Cᵢ(t−centroid) and y'=Cᵢy. An origin-preserving Q-isomorphism of short Weierstrass curves in characteristic zero has coefficient scalings by a rational fourth and sixth power. Dividing its B equality by its A equality therefore shows Cᵢ/dᵢ is a rational square. This is the step that equality of j-invariants alone would not supply.

The complementary twist squareclasses are thus (3,7,−1,2). The four original classes are uniquely recovered by multiplying the other three complementary classes: in Q×/Q×² the matrix J−I has square equal to the identity in dimension four. The resulting representatives are

    (c₀,c₁,c₂,c₃)=(−14,−6,42,−21).

For these representatives the complementary products are (5292,12348,−1764,3528), namely (3,7,−1,2) times 42². Relative to the published dᵢ, their square factors are (630,2058,42,336)². Thus the arithmetic comparison has exact rational coordinate scalings, not only a squarefree-factor computation.

## Identification and what it does not establish

Subject to the precise geometric inputs above and the standard quotient/Jacobian/Kummer facts explicitly applied here, this proves a Q(t)-isomorphism

    Q(X) ≅ Q(t)(√(−14t), √(−6(t−32)), √(42(t−76832)), √(−21(t+343))).

It does not merely assert that four matching j-invariants determine a W-cover: the full arithmetic Jacobian isomorphisms determine four independent character squareclasses.

The Lean package verifies the literal coefficient identities, general complementary-squareclass recovery, and the actual Q(t)-algebra equivalence of four-root fields produced by those squareclasses. Its final theorem takes the four actual rational short-Weierstrass coefficient scalings as explicit hypotheses. It does not yet formalize the source PEL curve, its W quotient and character fields, or the genus-one Jacobian quotient argument that supplies those hypotheses. Accordingly the unconditional source-model bridge in Lean remains open. Integral smooth/proper models, infinity normalization, good-reduction support and the final Diophantine theorem are separate tasks. The constants have no prime factors outside {2,3,7}, but that observation by itself is not a theorem of good reduction.
