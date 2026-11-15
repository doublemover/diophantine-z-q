# Produce local free frames from finite generation

Isolated source candidate, no local Lean or active packet. Independent review pending.

The actual valuation integer ring is `ActualFinitePlaceIntegers318.Integers w`. A supplied embedded submodule M that is finitely generated and contains a specified nonzero original section now yields a constructed principal generator and free frame. The proof augments a finite generating set by that section, selects a member of maximal finite-place norm, uses the exact existing valuation-ring membership criterion to put every generator in its principal lattice, and proves the reverse inclusion from membership in M. The selected generator is nonzero because its norm dominates the nonzero section's norm.

No free-frame, rank-one, principal-ideal or invertibility premise is supplied. No completion, alternate valuation normalization or new generic-frame identification is used. The final frame is transferred across a proved equality of embedded submodules, not an arbitrary abstract isomorphism.

`OriginalFiniteModelFrames318` instantiates this construction at every excluded place with the actual original a0. It produces the already source-reviewed `ModelFrames` input and proves that the assembled bad-place lattice is still exactly the supplied model. The original pair membership is retained, so the separately constructed defect remains meaningful and is not forced to1.

Remaining assumptions are explicit: the actual geometric bad-model submodules, their finite generation (for example from a separately proved coherent model), and original-section membership. This does not construct those models or prove global coherence. Actual Hodge determinant/metrics, normalized all-place KS comparison maps, archimedean inputs and quantitative bad-defect control remain open. No geometric realization, metric or final height conclusion is asserted.

Native primary APIs are pinned to Mathlib56a00585: Submodule.FG is a finite-span witness, Finset.exists_max_image supplies the actual finite maximum, and LinearEquiv.ofEq transports across exact submodule equality. The actual field-ring/norm interfaces and source-reviewed previous map slice are preserved in primary/. Hosted validation remains blocked by the predecessor CommonRestriction frontier; do not introduce a redundant active packet or promote a scratch result.
