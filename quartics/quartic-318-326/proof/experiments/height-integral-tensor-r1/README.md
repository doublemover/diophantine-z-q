# Integral cotangent tensors at a reduced vertical DVR

Draft only. Local Lean compilation has not been run. Hosted strict checking and independent source acceptance are pending. The accepted progress snapshot and manuscript are unchanged.

## New prerequisite

The existing `FractionSourceSections318.vertical_sections` proves integral scalar coefficients in an actual integral Kähler frame. This packet lifts that result to actual cotangent tensor-square elements:

- `IntegralCotangentTensor318.map` maps the integral tensor square to the generic tensor square. It is constructed using the established generic frame, then identified on every pure tensor with the original Kähler map on both factors. It is injective and independent of the chosen integral frame.
- `integral_iff` proves that a generic tensor belongs to the image of this integral tensor map exactly when its coefficient in the induced tensor frame is in the original local ring. This is an equality of the actual tensor lattice with the coefficient criterion, not a separately supplied scalar-lattice identification.
- `VerticalCotangentSections318.q0` and `q1` are actual tensors J²(dt tensor dt)/P(t) and t times that tensor. Their coefficients are proved equal to the original `VerticalSection318` coefficients. `integral_sections` constructs integral tensor preimages using the existing DVR theorem.

## Boundaries

The actual integral rank-one Kähler frame and irreducibility of the rational prime in the vertical DVR remain required. No semistable/maximal-stack model is constructed. No comparison with the original global bicanonical sheaf, codimension-two extension, special-point pullback, finite-place norm, PEL family or KS isometry is asserted. These are subsequent geometric obligations.

The field expressions use totalized division, as does the predecessor scalar theorem. Their interpretation as evaluations of the rational differential requires P(t) nonzero. At P(t)=0 the totalized zero expression is not claimed to establish regularity at a branch point. Horizontal regularity needs the separate existing branch-chart argument.

The classical source read is `docs/sources/quartic_v10.tex` lines 7015–7037: the literal bicanonical pair, scaling J², vertical differential inequality, and regularity argument. The frame/derivation and DVR scalar prerequisite already exists in the accepted sources; this packet does not claim to newly prove those earlier steps.

## Application contract

1. Objects and coefficients. The integral object is Ω(B/R) tensor_B Ω(B/R); the generic object is Ω(K/R) tensor_K Ω(K/R), with K the actual fraction field of B. Both use the original relative base R.
2. Quantifiers. The map and membership criterion quantify over every integral or generic tensor, not only the two distinguished sections. Frame independence covers every pair of integral frames. The application covers both literal source sections and every t, with the stated totalized-division boundary.
3. Domain. The generic frame is constructed by FractionKaehlerFrame318 from the integral frame. B is a domain and K its fraction field. The source DVR application additionally requires a reduced rational-prime uniformizer. No field or integral-model identity is inferred from the arithmetic point cover.
4. Map directions. Integral tensors map to generic tensors; map_pure proves compatibility with both original differential maps. Frame independence is proved by tensor induction. Injectivity is deduced from the actual fraction-field embedding, and coefficient membership is equivalent to existence of a tensor preimage.
5. Scalars. The tensor frame sends a pure tensor to the product of its two differential coefficients. Hence the derivative enters squared, and the scale is J² with J=2765952000. q1=t q0 is retained exactly. No norm or factor 32 is dropped.
6. Consuming object. q0_coefficient and q1_coefficient identify actual generic tensors with precisely VerticalSection318.section0 and section1 for the constructed fraction derivation. The DVR scalar existence theorem is consumed through integral_iff to produce actual integral tensor preimages.
7. Required hypotheses. FractionSourceSections318.vertical_sections requires an actual integral Kähler frame and a rational-prime uniformizer. Both remain explicit; preservation of the integral ring, the generic frame and the derivative valuation inequality are supplied by prior constructed theorems, not reintroduced as assumptions.
8. Historical status. The original source supplies the classical vertical argument; existing accepted Lean modules supply its scalar local algebra. This packet adds only the intrinsic tensor-lattice consequence. Global model realization and regularity-based extension remain pending, and no historical acceptance record is altered.
9. Validation. Every packet and consumed source is hash-bound. Static closure and source checks do not prove elaboration or the mathematical application. Hosted strict compilation, recursive private-inclusive axiom checking and distinct source acceptance remain pending. No author-generated independent approval is supplied.
