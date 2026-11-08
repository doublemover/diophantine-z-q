# Intrinsic invariant differential and canonical Hodge comparison

This packet constructs a genuine global invariant differential in the previously constructed universal relative differential sheaf of the completed Weierstrass family. It identifies that actual sheaf with the earlier invariant structure line, and proves that the pre-existing canonical Hodge-to-identity evaluation map is invertible over domain bases. The literal open-j family is included for nonzero level.

## Construction and scope

1. The affine universal differential comparison is normalized on every universal differential. Algebra-structure and coefficient equalities transport a datum containing both the comparison and its normalization, preserving the exact derivative formula.
2. Actual open-chart restriction sends the algebraic differential of a function to its ambient intrinsic derivative. The coordinate-change formula follows on universal differentials and then on all Kähler differentials by generation.
3. The three actual chart sections are the x-chart form `-dy/J0`, the finite-y form `dx/(2y)`, and the infinity form `-du/J`. The previously checked algebraic overlap equations are transported into the intrinsic ambient module sheaf.
4. Compatibility is proved on the **full actual intersections**, using the previously checked image theorems for the product localization and finite/infinity common localization. Under the unit-discriminant hypothesis, every x/infinity intersection point lies in the finite-y chart; restricting the other two checked equalities therefore supplies compatibility on that full intersection as well. A dense-open comparison is not substituted for gluing.
5. The actual sheaf condition glues these sections. Every ambient subopen of each chart has a freely generating restriction, proved from the genuine normalized chart frame. Isomorphism detection on the basis of all such subopens then gives the actual global frame.
6. Over a domain, the checked `ProperAffineSections318.family_unitMap_isIso` supplies the structure-sheaf pushforward isomorphism. The existing adjunction/evaluation criterion then proves invertibility of the **canonical existing** `IntrinsicHodgeComparison318.hodgeToIdentity` morphism. Its identification with the actual infinity cotangent and a free base line follows.

The global intrinsic differential frame assumes only a commutative base and invertible Weierstrass discriminant. The Hodge evaluation result additionally assumes that the base is a domain. It does not claim the corresponding pushforward theorem for arbitrary nonreduced/non-domain bases. For the literal open-j base, a direct localization-domain proof supplies the domain assumption when the level is nonzero.

## Main endpoints

- `IntrinsicGlobalFrame318.invariant`: actual global intrinsic differential section.
- `IntrinsicGlobalFrame318.invariant_restrict`: its three exact chart restrictions.
- `IntrinsicGlobalFrame318.frame`: actual intrinsic Omega is isomorphic to the earlier invariant line.
- `IntrinsicGlobalFrame318.frame_inv_local`: its inverse sends the unit-line chart generator to the specified intrinsic invariant differential.
- `IntrinsicHodgeIsomorphism318.hodgeToIdentity_isIso`: the actual canonical evaluation morphism is invertible.
- `IntrinsicHodgeIsomorphism318.hodgeToIdentityIso_hom`: the produced isomorphism has exactly that canonical morphism.
- `IntrinsicHodgeIsomorphism318.hodgeToCotangent` and `hodgeFrame`.
- `LiteralIntrinsicHodge318.differentialFrame`, `hodgeToIdentity_isIso`, and `hodgeFrame`.

## Verification

`module-order.txt` gives the complete source order. `verify.sh` acquires the shared exclusive compilation lock and invokes `replay.sh`, which strictly rechecks every source and then recursively checks every declaration in every packet module for axiom dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted. `receipt.json` binds sources, logs, scripts, and upstream receipts to SHA-256 hashes. The source is standalone proof work; no shared repository, branch, or pinned Mathlib source was modified. No new copy of a Mathlib declaration is introduced here.

Lean is 4.35.0 with `debug.skipKernelTC=false`, one compilation thread, and pinned Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Remaining boundary

This is the complete intrinsic-differential/Hodge comparison for the actual smooth completed family in the stated scope. It does not construct a compact modular or PEL source, a canonical/bicanonical source identification, a global-source Kodaira–Spencer map, an analytic or metric comparison, or the final desired realization theorem. Those remain separate geometric inputs.
