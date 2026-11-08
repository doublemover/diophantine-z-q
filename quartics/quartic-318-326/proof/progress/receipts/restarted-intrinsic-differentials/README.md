# Intrinsic relative differentials and the actual Hodge comparison map

This isolated packet recovers and completes the previously unfinished intrinsic differential construction. It does not modify the repository, publish a branch, or open a PR.

## New intrinsic construction

`UniversalSheafDifferentials318.omega` is the actual O-module sheafification of the presheaf assigning universal relative Kähler differentials to every open. `D` is an actual derivation into that sheaf. `universalEquiv`, `desc_fac`, `hom_ext`, and `existsUnique_desc` establish the full universal property against every actual O-module sheaf, not only a selected cover, free sheaves, or quasi-coherent sheaves.

`FamilyIntrinsicDifferentials318` obtains the coefficient maps from the actual structure morphism of the previously glued Weierstrass scheme. `familyOmega`, `familyD`, and `family_universal` therefore exist intrinsically on that global family. The literal open-j specialization is included. The construction requires neither an assumed rank-one frame nor a discriminant hypothesis.

`IntrinsicUniversalComparison318.isoOfUniversal` proves uniqueness up to the uniquely normalized actual sheaf isomorphism for any other genuine global universal sheaf derivation. Its hypothesis is explicit. This criterion does not construct a universal derivation on the older descent line by itself.

## Actual pushforward and identity map

`IntrinsicHodgeComparison318.hodge` is the actual Scheme.Modules pushforward of the intrinsic differential sheaf. `identityCotangent` is its actual pullback along the global identity. `hodgeToIdentity` is the canonical morphism between them, constructed from the pullback/pushforward counit and the exact section equation. Naturality and the adjunction-unit normalization on pulled-back sheaves are proved. The latter gives an actual splitting for evaluation on pulled-back sheaves.

`StructurePushforwardSplit318` constructs the actual O-base morphism `O -> pi_* O` and evaluation at the identity, proves their composite is the identity, and deduces that the former is a monomorphism. These statements hold for any actual section, and specialize to the actual family without additional hypotheses.

## Exact remaining boundaries

The earlier global-differential-gluing packet constructs the global structure line with normalized Kähler forms on the actual full chart intersections. This packet constructs intrinsic Omega and its universal derivation, but does not yet identify that intrinsic sheaf with the earlier descent line. That requires an actual affine sheafification/tilde comparison compatible with the canonical derivative maps, followed by the existing full-overlap gluing data.

The structure-sheaf splitting is not surjectivity. No theorem here asserts `pi_* O = O`, that `hodgeToIdentity` is invertible, or that intrinsic Omega is free of rank one. Properness and geometrically integral/connected fibers were proved in earlier packets, but their cohomological/global-functions consequence is not established by this packet.

Nor does this packet identify the relative elliptic-family Hodge line with the compact modular/PEL base canonical or bicanonical line, perform algebraic/analytic or metric comparison, construct the final global source realization, or prove unconditional arithmetic soundness.

## Verification and dependency provenance

Run `bash verify.sh`. It obtains the shared exclusive heavy-compilation lock, strictly rebuilds the packet sequentially with `debug.skipKernelTC=false`, then audits every declaration in every packet module, including private/generated declarations. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted recursively. Frozen upstream modules are imported, not all rebuilt by this packet.

Three previously missing cached Mathlib modules are compiled as local copies to avoid changing a shared checkout/cache. They are exact pinned source bodies; only the two dependency imports in the third copy are changed to local names. `mathlib-source-provenance.json` records canonical names, paths, hashes, and exact transformations. For repository integration, compile those canonical pinned modules and replace the single `MathlibPresheafDifferentials318` import in `UniversalSheafDifferentials318` by `Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf`; the mathematical proof bodies are separable from this cache workaround.
