module
public import ProjectiveLineOverlap318
public import ClutchedModuleFrames318
public section
noncomputable section
namespace ProjectiveLineOOne318
open AlgebraicGeometry CategoryTheory Polynomial
open ProjectiveLineOverlap318 ClutchedModule318 ClutchedModuleFrames318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- The literal transition function t=X0/X1, as an actual regular function
on the entire projective-line overlap. -/
@[expose] def transition : Γ(Spec (CommRingCat.of A),⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).inv t

theorem transition_unit : IsUnit transition := by
  have ht : IsUnit t := tUnit_coe ▸ tUnit.isUnit
  exact ht.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem finite_intersection :
    JLineAtlas318.chart ℚ 1 ⁻¹ᵁ (JLineAtlas318.chart ℚ 0).opensRange=finiteInclusion.opensRange := by
  rw [←Scheme.Hom.image_top_eq_opensRange,chart_one_preimage_zero,finite_range]

theorem infinity_intersection :
    JLineAtlas318.chart ℚ 0 ⁻¹ᵁ (JLineAtlas318.chart ℚ 1).opensRange=infinityInclusion.opensRange := by
  have h := congrArg (fun U => JLineAtlas318.chart ℚ 0 ⁻¹ᵁ U) full_intersection
  rw [Scheme.Hom.preimage_inf,Scheme.Hom.preimage_opensRange,inf_top_eq] at h
  simp only [embedding,maps_agree,Scheme.Hom.opensRange_comp,Scheme.Hom.preimage_image_eq] at h
  exact h

/-- A genuine projective-line sheaf built by gluing the two standard unit
modules with transition t. This is the O(1) convention e0=t*e1, not O(-1). -/
@[expose] def line : (ProjectiveJLine318.scheme ℚ).Modules :=
  sheaf (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
    finiteInclusion infinityInclusion maps_agree.symm transition

/-- The actual full finite-chart trivialization. -/
@[expose] def finiteFrame : line.restrict (JLineAtlas318.chart ℚ 1) ≅
    unit (Spec (CommRingCat.of ℚ[X])) :=
  firstFrame (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
    finiteInclusion infinityInclusion maps_agree.symm transition transition_unit infinity_intersection

/-- The actual full infinity-chart trivialization. -/
@[expose] def infinityFrame : line.restrict (JLineAtlas318.chart ℚ 0) ≅
    unit (Spec (CommRingCat.of ℚ[X])) :=
  secondFrame (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
    finiteInclusion infinityInclusion maps_agree.symm transition finite_intersection

/-- The frames cover every actual point of the projective line. -/
theorem frames_cover (x : ProjectiveJLine318.scheme ℚ) :
    (∃ y, JLineAtlas318.chart ℚ 1 y=x) ∨ (∃ y, JLineAtlas318.chart ℚ 0 y=x) := by
  have hx : x∈(⊤:(ProjectiveJLine318.scheme ℚ).Opens) := trivial
  rw [←JLineAtlas318.standard_opens_cover ℚ] at hx
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  rw [←JLineAtlas318.chart_range] at hi
  fin_cases i
  · exact Or.inr hi
  · exact Or.inl hi
end ProjectiveLineOOne318
