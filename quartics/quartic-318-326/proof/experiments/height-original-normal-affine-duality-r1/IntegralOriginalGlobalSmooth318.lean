module
public import IntegralOriginalSmoothCharts318
public section
noncomputable section
namespace IntegralOriginalGlobalSmooth318
open AlgebraicGeometry CategoryTheory
open IntegralGluedModel318 IntegralGluedDifferentialFrames318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

/-- The original five-chart cover, with its concrete finite index type
exposed for source-local smoothness and with the original embeddings. -/
abbrev smoothCover (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    (scheme R c).OpenCover where
  I₀ := Option (Fin 4)
  X := chart R c
  f := embedding R c
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,inferInstance⟩
    intro x
    rcases frames_cover R c hN x with ⟨i,q,hq⟩|⟨q,hq⟩
    · exact ⟨some i,q,hq⟩
    · exact ⟨none,q,hq⟩

/-- Smoothness of the ORIGINAL structure morphism is proved on every
actual chart. It is not inferred from the existence of cotangent frames. -/
theorem smooth (h2 : IsUnit (2:R))
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    Smooth (structureMap R c) := by
  apply IsZariskiLocalAtSource.of_openCover (P:=@Smooth) (smoothCover R c hN)
  intro i
  cases i with
  | none =>
    change Smooth (infinityChart R c ≫ structureMap R c)
    rw [infinityChart_structure]
    exact (HasRingHomProperty.Spec_iff (P:=@Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (IntegralOriginalSmoothCharts318.infinity_smooth R c h2))
  | some i =>
    change Smooth (branchEmbedding R c i ≫ structureMap R c)
    rw [branch_structure]
    exact (HasRingHomProperty.Spec_iff (P:=@Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (IntegralOriginalSmoothCharts318.source_branch_smooth R c h2 i))
end IntegralOriginalGlobalSmooth318
