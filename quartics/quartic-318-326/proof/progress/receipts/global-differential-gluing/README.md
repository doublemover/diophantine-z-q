# Actual global differential gluing and identity cotangent

This isolated packet completes and strictly replays the seven previously unfinished global-invariant-line modules, then closes their actual-overlap geometry and constructs a genuine identity-cotangent comparison. It does not edit a repository, publish a branch, or open a PR.

## Actual global sheaf and actual local forms

`GlobalInvariantLine318.line` is the actual structure-module line on `WeierstrassGluing318.scheme`, not a new coefficient record. Its actual unit section restricts under genuine O-module isomorphisms to `-dy/J0`, `dx/(2y)`, and `-du/J` in the respective universal relative Kähler modules. The normalized frames derive from the already constructed Jacobian-localization frames and proved unit values.

`InvariantTransition318` transports the actual normalized frames using the actual canonical differential restriction morphisms. Equality on the actual global unit generator determines the entire sheaf morphism. `GlobalInvariantCompatibility318` then proves equality of the entire frame morphisms on the concrete x/y, finite/infinity, and three-chart localizations. These are the canonical universal-differential maps previously identified with genuine restriction isomorphisms, not assumed or arbitrary abstract frame identifications.

The actual three-chart cover is proved when the literal discriminant `-16*(4*A^3+27*B^2)` is a unit, and specializes without an extra hypothesis to the previously constructed literal open-j family.

## Full actual intersections, not only common subopens

`ActualChartIntersections318` identifies the product localization's image with the full finite x/y intersection in the global scheme. It also proves that two points of the original finite and infinity charts become equal in the actual scheme pushout exactly when they come from its original overlap.

`FullInfinityIntersection318` proves the exact ambient commutative diagrams and shows that the previously checked finite-y/infinity differential common ring covers the full intersection of those actual chart images. This requires no characteristic or discriminant assumption.

`FullTripleIntersection318` proves that the actual triple localization covers the full three-chart intersection. With the actual discriminant invertible, 2 is necessarily a unit. Since y is invertible on the original finite/infinity overlap, the entire x/infinity intersection lies in the finite-y chart. The actual triple ring is therefore the full x/infinity pairwise intersection, not merely a dense part of it. No field, density, or nonempty-overlap premise is used.

`ActualOverlapPullbacks318` upgrades the full-image results and exact ambient commutative diagrams to genuine categorical `IsPullback` theorems for all three pairwise overlap schemes. Together with the actual local sheaf isomorphisms, full sheaf-map equalities, and covering theorem, this supplies an explicit global line realizing the relative-differential descent data on the full actual chart cover.

## Genuine cotangent at the identity

`IdentityCotangent318.infinity_factorization` identifies the previously constructed actual global identity with its exact smooth infinity-chart factorization. `cotangent` is the actual Scheme.Modules pullback of that chart's genuine relative differential sheaf to the base. `cotangentFrame` is a genuine O-base isomorphism obtained by pulling back the normalized actual differential frame. `globalLineToCotangent` identifies the actual global line's pullback at the global identity with this cotangent sheaf, using the exact factorization and actual pullback/restriction functor comparisons. The literal open-j specialization is included.

Two Mathlib modules needed for the generic pullback-of-unit isomorphism were absent from the local precompiled cache. They are compiled locally as `MathlibFinalType318` and `MathlibPullbackFree318`. The former is an exact source copy of Mathlib.CategoryTheory.Limits.Final.Type. The latter differs from Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree only by its import pointing to that local copy. Their declarations are included in the exhaustive audit; the shared Mathlib checkout/cache is untouched.

## Exact remaining boundaries

This packet proves an explicit global line with genuine canonical differential descent data and a genuine cotangent-at-identity comparison. It does not define a new global universal derivation or prove a global universal property for a named intrinsic scheme Ω object. It does not prove the Hodge pushforward identification `pi_* Omega = e^* Omega`, nor `pi_* O = O`, compatibility with group translation, or base-change theorems for that pushforward. Properness and geometric fiber integrality/connectedness are already proved independently in `CubicClosedImmersion318.structure_proper` and `GeometricFibers318.geometrically_integral` / `geometrically_connected`; this packet does not derive the required pushforward/cohomological comparison from those results.

It does not identify the relative elliptic-family differential line with the canonical or bicanonical line of the compact modular/PEL base. Algebraic/analytic comparison, source-model comparison, metric identification, and the remaining global source realization remain separate. No unconditional arithmetic soundness conclusion is claimed.

## Verification

Run `bash verify.sh`. Every one of the 14 modules is rebuilt with `debug.skipKernelTC=false`. The explicit `import all` audit traverses every generated/private declaration in every packet module and recursively accepts only `propext`, `Classical.choice`, and `Quot.sound`. The receipt records the exact counts, hashes, and upstream receipts. An exhaustive packet audit is not an independent reproof or rebuild of every frozen upstream dependency.
