# Actual projective Weierstrass completion

This packet constructs an actual morphism from the previously checked two-chart Weierstrass scheme into the actual homogeneous `Proj` plane, proves it is a closed immersion, and derives properness and separatedness over the original base ring. All rings and schemes are actual Mathlib objects. There is no supplied properness, projective-model, chart-overlap, or closed-immersion hypothesis.

## Exact scope

For every commutative ring R and A, B in R, the source is the unchanged `WeierstrassGluing318.scheme A B`, glued from

- `Spec R[x,y]/(y² - x³ - Ax - B)`,
- `Spec R[x,z]/(z - x³ - Axz² - Bz³)`,

along their actual localizations at y and z, with the previously checked reciprocal-coordinate isomorphism. The target is `Proj (homogeneousSubmodule (Fin 3) R)`, with coordinates X, Y, Z and its actual structure morphism to `Spec R`.

The constructed embedding has the homogeneous cubic support

`Y²Z - X³ - AXZ² - BZ³ = 0`.

Its inverse images over D(Z) and D(Y) are proved to be the actual finite and infinity quotient charts by Cartesian squares of schemes. Thus the morphism is locally a closed immersion on the ambient open containing its image. A homogeneous prime containing the cubic and both Y and Z would contain X³ and then X, contradicting relevance. This explicitly excludes a missing X-only point. Conversely every prime on the homogeneous cubic lifts through one of the actual polynomial quotient spectra. The image is therefore exactly the closed homogeneous zero locus, and the actual morphism is a closed immersion.

The properness proof composes this closed immersion with Mathlib's proper structure morphism for a finitely generated homogeneous Proj. Its degree-zero ring is explicitly identified with R; the final map is the original glued base map, not an unbound surrogate.

## Main checked APIs

- `ProjectiveChart318.chartEquiv R σ j`: for any finite decidable index type, actual degree-zero homogeneous localization at X_j is R-algebra-isomorphic to the polynomial ring in the other variables. Both inverse laws and homogeneous fraction formulas are checked over arbitrary commutative rings.
- `ProjectivePlane318.structure_proper R`: actual proper Proj plane over R.
- `ProjectiveAtlas318.cover R`: the actual three standard polynomial affine charts cover that plane; each chart commutes with the original base map.
- `ProjectiveEvaluation318.chart_compatibility`: actual Spec maps through different invertible-coordinate homogeneous localizations agree in Proj.
- `CubicProjectiveMap318.embedding A B`: actual globally glued cubic morphism.
- `CubicChartGeometry318.embedding_over_base`: exact compatibility with the original glued base map.
- `CubicChartGeometry318.finite_pullback` and `infinity_pullback`: scheme-theoretic chart inverse images.
- `CubicClosedImmersion318.embedding_range`: exact homogeneous cubic support.
- `CubicClosedImmersion318.embedding_closed`: actual closed immersion.
- `CubicClosedImmersion318.structure_proper`, `structure_separated`, `infinity_closed`: actual proper/separated structure map and closed infinity section.
- `CubicClosedImmersion318.literal_proper N`: unconditional specialization to the literal `OpenJModel318.Base N` family.

The properness and closed-immersion statements do not require the discriminant to be a unit. Smoothness and relative dimension one are supplied by the separately frozen infinity/affine/dimension packets when their stated hypotheses hold; those hypotheses are discharged for the literal OpenJ model.

## Reproduction and remaining boundary

Run `bash projective-weierstrass-scheme/build.sh` from the shared workspace. The script uses Lean 4.35.0 and the pinned Mathlib revision recorded in the receipt, rebuilds all seven modules with kernel checking enabled, and audits every declaration in those modules recursively against only `propext`, `Classical.choice`, and `Quot.sound`. Required project dependency packets are listed explicitly in `LEAN_PATH`.

This constructs the actual closed projective cubic through its affine quotient charts and a closed immersion into the homogeneous Proj plane. It does not introduce or assert an identification with an additional, independently defined homogeneous-quotient `Proj` object. No such extra object is needed for the proved properness.

A full relative elliptic group law, the relative primitive-torsion scheme and its local splitting, and the remaining global `RefinedGeometricRealization` are not asserted by this packet. The separate global negation and ordinary-chord morphisms are not promoted here to a full group-scheme law.
