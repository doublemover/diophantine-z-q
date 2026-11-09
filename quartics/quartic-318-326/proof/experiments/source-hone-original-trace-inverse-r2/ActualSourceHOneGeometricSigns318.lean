module
public import OriginalSignChartPreservation318
public import ActualSourceHOneCharacterAction318
public import ActualSourceHOneResidueBasis318

public section
noncomputable section
namespace ActualSourceHOneGeometricSigns318
open AlgebraicGeometry CategoryTheory
open ActualSourceHOnePresentation318 OriginalSignChartPreservation318
open ActualSourceHOneRationalSpanning318
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original geometric sign pullback is computed on the actual whole-overlap boundary. -/
theorem pullback_boundary (b : Fin 4 → Bool) (x : ActualSourceHOneCoordinates318.OverlapRing) :
    SchemeSourceCohomology318.pullback (signMap b) 1 (ActualSourceHOneCoordinates318.boundary x) =
      ActualSourceHOneCoordinates318.boundary (ContactGlobalSigns318.openEquiv units b x) := by
  change SchemeSourceCohomology318.pullback (signMap b) 1
    (MayerVietorisSectionKernel318.sectionBoundary (StructureAdditiveSheaf318.sheaf Source)
      finiteOpen infinityOpen cover (ActualSourceHOneCoordinates318.overlapSections x)) = _
  rw [StableCoverBoundary318.pullback_stable_boundary (signMap b) finiteOpen infinityOpen cover
    (finite_preimage b) (infinity_preimage b),overlap_sections]
  rfl

/-- The formerly quotient-defined sign action equals the original scheme-cohomology pullback on all H1. -/
theorem geometric_action (b : Fin 4 → Bool) (y : ActualSourceHOnePullbacks318.SourceHOne) :
    SchemeSourceCohomology318.pullback (signMap b) 1 y = ActualSourceHOneCharacterAction318.action b y := by
  obtain ⟨x,rfl⟩ := ActualSourceHOneCoordinates318.boundary_surjective y
  rw [pullback_boundary,ActualSourceHOneCharacterAction318.action_boundary]

/-- The five nonzero coordinates carry the asserted characters under the actual geometric maps. -/
theorem geometric_character (i : SourceHOneCharacterIndices318.Index) (b : Fin 4 → Bool) :
    SchemeSourceCohomology318.pullback (signMap b) 1
      (ActualSourceHOneCharacterAction318.characterClass i) =
    SourceHOneCharacterIndices318.epsilon i b • ActualSourceHOneCharacterAction318.characterClass i := by
  rw [geometric_action,ActualSourceHOneCharacterAction318.action_characterClass]

/-- Geometric projectors use the original scheme-cohomology pullbacks with the exact full16 normalization. -/
theorem projector_geometric (i : SourceHOneCharacterIndices318.Index) (y : ActualSourceHOnePullbacks318.SourceHOne) :
    ActualSourceHOneCharacterProjectors318.projector i y =
      (1 / 16 : ℚ) • ∑ b : Fin 4 → Bool, SourceHOneCharacterIndices318.epsilon i b •
        SchemeSourceCohomology318.pullback (signMap b) 1 y := by
  simp only [ActualSourceHOneCharacterProjectors318.projector,LinearMap.smul_apply,
    LinearMap.sum_apply,geometric_action]

end ActualSourceHOneGeometricSigns318
