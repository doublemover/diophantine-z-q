# Actual module morphisms from the full affine basis

This98-source packet keeps the exact96-source `affine-open-chart-coherence-r2` closure, including its versioned1ca producer repairs, and adds two substantive basis-extension sources.

`AffineBasisModuleMaps318` constructs an actual sheaf-of-modules morphism from linear maps on every original affine open, natural only for nested affine opens. Mathlib's genuine sheaf basis-extension equivalence first constructs the additive map on all opens. The original sheaf separation law then proves linearity over every original section ring. The original affine components are recovered literally and determine the map uniquely.

`AffineBasisModuleIsomorphisms318` derives inverse naturality, builds actual global sheaf isomorphisms, and proves that identities, compositions and cocycles are detected on the entire affine basis. Arbitrary pair intersections need not be affine.

This supplies the general non-affine-intersection morphism-extension mechanism needed to assemble the existing nested-chart transition comparisons. The remaining adapter must construct these affine component maps from the exact original restricted chart lines, preserving original open-image and restriction comparisons. This packet does not falsely claim that adapter or global effective descent is already complete.

No local Lean compilation. Static bindings and the audit-history self-test are separate from hosted elaboration and recursive axiom audit, which remain pending. The accepted snapshot is unchanged. No represented Picard/Jacobian or full arithmetic result is asserted.

## Revision after bounded source review

Remove the redundant rfl after all three exact affine-component rewrites in hom_comp. The final equality is definitional and the rewrite tactic may already discharge it. No theorem or construction changes. Hosted validation remains pending.
