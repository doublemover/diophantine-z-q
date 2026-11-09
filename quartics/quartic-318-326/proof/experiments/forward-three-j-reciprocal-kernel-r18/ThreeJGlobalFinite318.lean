module
public import ProjectiveLineLaurentComplement318
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public section
noncomputable section
namespace ThreeJGlobalFinite318
open AlgebraicGeometry CategoryTheory
open ThreeJFiniteLaurentMap318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Properness concerns the actual original projective map, from its exact
Q-structure identity and the existing proper projective source structure. -/
instance map_proper : IsProper ThreeProjectiveJMap318.map := by
  letI : IsProper (ThreeProjectiveJMap318.map ≫ ProjectiveJLine318.structureMap ℚ) := by
    rw [ThreeProjectiveJMap318.over_Q]
    infer_instance
  exact IsProper.of_comp _ (ProjectiveJLine318.structureMap ℚ)

/-- Every scheme-theoretic topological fiber is finite. The proof uses the
actual finite Laurent-map comparison plus the proved finite source complement;
it does not infer this from finiteness of complex-valued point fibers. -/
theorem finite_scheme_fiber (y : ProjectiveJLine318.scheme ℚ) :
    Set.Finite (ThreeProjectiveJMap318.map ⁻¹' {y}) := by
  have hr : Set.Finite ((ProjectiveLineOverlap318.embedding ≫
      ThreeProjectiveJMap318.map) ⁻¹' {y}) := by
    rw [original_scheme_square]
    exact finiteTargetMap.finite_preimage
      ((Set.subsingleton_singleton.preimage
        (JLineAtlas318.chart ℚ 1).isOpenEmbedding.injective).finite)
  apply ((hr.image ProjectiveLineOverlap318.embedding).union
    ProjectiveLineLaurentComplement318.complement_finite).subset
  intro x hx
  by_cases h : x ∈ Set.range ProjectiveLineOverlap318.embedding
  · obtain ⟨z,hz⟩ := h
    exact Or.inl ⟨z,by
      change ThreeProjectiveJMap318.map (ProjectiveLineOverlap318.embedding z)=y
      rw [hz]
      exact hx,hz⟩
  · exact Or.inr h

instance map_locallyQuasiFinite : LocallyQuasiFinite ThreeProjectiveJMap318.map :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ finite_scheme_fiber

/-- Scheme-theoretic finiteness of the exact global level-three j morphism.
This closes the all-source/all-target finiteness step using properness and
quasi-finiteness, not a generic-only or complex-points-only assertion. -/
theorem map_finite : IsFinite ThreeProjectiveJMap318.map :=
  IsFinite.of_isProper_of_locallyQuasiFinite _

end ThreeJGlobalFinite318
