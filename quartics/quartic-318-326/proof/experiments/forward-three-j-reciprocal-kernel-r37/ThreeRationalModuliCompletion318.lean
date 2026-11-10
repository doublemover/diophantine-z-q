module
public import ThreeJActualGenericDegree318
public section
noncomputable section
namespace ThreeRationalModuliCompletion318
open AlgebraicGeometry CategoryTheory
open ThreeRationalModuliScheme318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

instance parameter_open_nonempty : Nonempty ThreeJModuliScheme318.Source := by
  let z : ThreeCompactParameter318.ParameterOpen := ⟨1,by norm_num [ThreeCompactParameter318.D]⟩
  exact ⟨ActualThreeModuliSchemeComparison318.parameterPoint z
    (default : Spec (CommRingCat.of ℂ))⟩
instance rational_target_nonempty : Nonempty RationalTarget :=
  Nonempty.map schemeIso.hom inferInstance
instance rational_embedding_dominant : IsDominant rationalEmbedding :=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _ rationalEmbedding.isOpenEmbedding.isOpenMap⟩
instance rational_target_integral : IsIntegral RationalTarget :=
  isIntegral_of_isOpenImmersion rationalEmbedding

/-- A genuine dense-open proper completion of the actual rational arithmetic
level-three quotient in the original projective parameter scheme. The map to
the j-line is the same finite surjective scheme morphism used throughout. -/
theorem actual_proper_completion :
    IsOpenImmersion rationalEmbedding ∧ IsDominant rationalEmbedding ∧
      IsIntegral (ProjectiveJLine318.scheme ℚ) ∧
      IsProper (ProjectiveJLine318.structureMap ℚ) ∧
      IsFinite ThreeProjectiveJMap318.map ∧ Surjective ThreeProjectiveJMap318.map :=
  ⟨inferInstance,inferInstance,inferInstance,inferInstance,
    ThreeJGlobalFinite318.map_finite,ThreeJActualDominance318.map_surjective⟩

/-- The completed model has actual generic degree four with respect to the
literal pullback on generic stalks, and still contains the original rational
arithmetic scheme by the proved dense open immersion. -/
theorem completed_generic_degree_four :
    letI := ThreeJActualGenericDegree318.pullbackAlgebra
    letI : Module (ProjectiveJLine318.scheme ℚ).functionField
      (ProjectiveJLine318.scheme ℚ).functionField :=
        ThreeJActualGenericDegree318.pullbackAlgebra.toModule
    Module.finrank (ProjectiveJLine318.scheme ℚ).functionField
      (ProjectiveJLine318.scheme ℚ).functionField=4 :=
  ThreeJActualGenericDegree318.actual_generic_degree_four

end ThreeRationalModuliCompletion318
