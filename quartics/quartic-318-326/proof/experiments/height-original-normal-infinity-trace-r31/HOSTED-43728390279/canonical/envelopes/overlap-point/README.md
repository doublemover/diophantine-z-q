# Actual full-overlap point localization-domain repair

INACTIVE SOURCE CANDIDATE; no local Lean or new kernel acceptance.

Own center81/parameter12 run43728390279 at a28f35d4c2678cbcd9633b289a8d0dd510cc0f5f independently passes62 complete modules, including GenericPoint and BranchSelection. Both fail OverlapPoint: first line34 leaves native Away.lift localization domain ?m unresolved against the actual tensor Overlap, with different unresolved ring dictionary paths and a note about unexposed OreLocalization.instAdd. Later wrong commonPoint argument/unknown-variable errors follow the failed definition. Failure7.932s/7.282s;33/43 later roots unreached. No partial failed-module declarations accepted.

The proposed bounded repair explicitly fixes S:=Overlap V c on the native Away.lift and on its source-evaluation theorem lift_eq, also naming the actual g/sourceQuartic in that theorem. The exact existing sourceAlgebra and whole_localization instances are retained, not replaced. No alternative ring/addition dictionary, source transport, cached ring structure, unit assumption or new point is inserted. This addresses the concrete unresolved localization-domain inference; whether remaining dictionary conversion succeeds must be established by hosted elaboration, not assumed from source inspection.

All declaration types/intended parameters and original source, quartic, signed roots, overlap/infinity coefficients and proofs otherwise stay exact. K/V ring universes remain independent. Full original punctured quartic overlap and original noninteger-t hypothesis remain; finite ramification and signed/zero integral-root boundary data are not restricted. No scalar cancellation, root/2 inversion, good-unit-locus surrogate, resource/trust/option change or root expansion.

Actual downstream InfinityExtension and PointCenter APIs remain unchanged and unreached. Trace owns any preventive same-byte propagation using its own receipt; center/parameter evidence is not borrowed for trace acceptance. No whole-model, intrinsic dualizing, regular/maximal-model, proper-gluing, all-place or GeometricRealization claim.
