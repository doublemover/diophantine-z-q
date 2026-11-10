module
public import PELOriginalBaseCompact318
public import PELQuotientBranchIsolation318
public import Mathlib.Topology.DiscreteSubset
public section
noncomputable section
namespace PELOriginalFiniteBranchImage318
open PELOriginalMaximalQuotient318 PELStabilizerLocusInvariant318
open PELQuotientBranchIsolation318 PELOriginalBaseCompact318
set_option maxHeartbeats 1500000

/-- The complete actual branch image is finite. This theorem does NOT
identify its cardinal with five; same-label orbit uniqueness remains distinct. -/
theorem original_branch_image_finite : branchImage.Finite := by
  letI : DiscreteTopology branchImage := discreteTopology_subtype_iff'.mpr (by
    intro q hq
    obtain ⟨W,hW,hqW,hWq⟩ := branch_image_neighborhood q hq
    refine ⟨W,hW,?_⟩
    ext z
    constructor
    · intro hz
      exact Set.mem_singleton_iff.mpr ((hWq z hz.1).mp hz.2)
    · intro hz
      have he := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨hqW,hq⟩)
  letI : CompactSpace branchImage := isCompact_iff_compactSpace.mp branch_image_closed.isCompact
  letI : Finite branchImage := finite_of_compact_of_discrete
  exact Set.toFinite branchImage
end PELOriginalFiniteBranchImage318
