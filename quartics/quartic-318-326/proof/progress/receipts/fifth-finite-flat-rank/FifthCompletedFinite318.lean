module
public import FifthReciprocalBaseSquare318
public import FifthTargetParameterRestriction318
public import SchematicEqualityExtension318
public import ProperFiniteFiberDescent318
public section
noncomputable section
namespace FifthCompletedFinite318
open AlgebraicGeometry CategoryTheory Polynomial SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthReciprocalBaseSquare318
set_option maxHeartbeats 180000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma infinity_composite:
    InfinityGlobalScheme318.chartEmbedding units≫FifthCompletedGlobal318.map≫FifthTargetParameter318.map=
      InfinityGlobalScheme318.chartEmbedding units≫ContactProjectiveModel318.modelMap units:=by
  rw [←Category.assoc,FifthCompletedGlobal318.on_infinity,
    FifthSourceInfinityScheme318.intoCompleted,Category.assoc,FifthSourceInfinityScheme318.toFinite,
    FifthTargetParameterRestriction318.source_infinity_restriction,
    ContactProjectiveModel318.modelMap,InfinityStructureMap318.chartEmbedding_over_contact_line]
  change Spec.map (CommRingCat.ofHom (Polynomial.aeval FifthSourceInfinityCoordinates318.u).toRingHom)≫
      JLineAtlas318.chart ℚ 0=
    Spec.map (CommRingCat.ofHom (ReciprocalInfinityBase318.chartMap units))≫
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] (ReciprocalInfinityBase318.ReciprocalOpen units)))≫
        JLineAtlas318.chart ℚ 0)
  rw [←Category.assoc,←Spec.map_comp,reciprocal_ring_square]
  rfl
 #check infinity_composite
/-- Exact factorization of the original finite contact map to the t-line. -/
@[reassoc] theorem over_t:FifthCompletedGlobal318.map≫FifthTargetParameter318.map=
    ContactProjectiveModel318.modelMap units:=by
  letI:IsIntegral (ContactGlobalSmooth318.Model units):=ContactProjectiveModel318.model_integral units
  letI:IsDomain (InfinityOpenChart318.OpenOrder units):=InfinityOpenChart318.openOrder_domain units
  letI:Nonempty (ReciprocalInfinityNormalization318.neighborhood units):=by
    change Nonempty (Spec (CommRingCat.of (InfinityOpenChart318.OpenOrder units)))
    infer_instance
  let j:=InfinityGlobalScheme318.chartEmbedding units
  letI:IsDominant j:=⟨IsOpenMap.denseRange_of_isPreirreducibleSpace j j.isOpenEmbedding.isOpenMap⟩
  letI:IsSchemeTheoreticallyDominant j:=IsSchemeTheoreticallyDominant.of_isDominant j
  have hb:(FifthCompletedGlobal318.map≫FifthTargetParameter318.map)≫ProjectiveJLine318.structureMap ℚ=
      ContactProjectiveModel318.modelMap units≫ProjectiveJLine318.structureMap ℚ:=by
    rw [Category.assoc,FifthTargetParameter318.over_Q]
    exact FifthCompletedGlobal318.over_Q
  exact SchematicEqualityExtension318.ext (ProjectiveJLine318.structureMap ℚ) hb j infinity_composite
#check over_t
lemma target_separated:IsSeparated FifthTargetParameter318.map:=by
  letI:IsSeparated (FifthTargetParameter318.map≫ProjectiveJLine318.structureMap ℚ):=by
    rw [FifthTargetParameter318.over_Q]
    exact CubicClosedImmersion318.structure_separated A B
  exact IsSeparated.of_comp _ (ProjectiveJLine318.structureMap ℚ)
#check target_separated
theorem finite:IsFinite FifthCompletedGlobal318.map:=by
  letI:=target_separated
  letI:IsFinite (FifthCompletedGlobal318.map≫FifthTargetParameter318.map):=by
    rw [over_t]
    exact ContactGlobalProper318.normalization_finite units
  exact IsFinite.of_comp FifthCompletedGlobal318.map FifthTargetParameter318.map
#check finite
theorem target_finite:IsFinite FifthTargetParameter318.map:=by
  letI:IsProper FifthTargetParameter318.map:=by
    letI:IsProper (FifthTargetParameter318.map≫ProjectiveJLine318.structureMap ℚ):=by
      rw [FifthTargetParameter318.over_Q]
      exact FifthCompletedProper318.target_proper_integral.1
    exact IsProper.of_comp _ (ProjectiveJLine318.structureMap ℚ)
  letI:=FifthCompletedProper318.surjective
  letI:IsFinite (FifthCompletedGlobal318.map≫FifthTargetParameter318.map):=by
    rw [over_t]
    exact ContactGlobalProper318.normalization_finite units
  exact ProperFiniteFiberDescent318.finite FifthCompletedGlobal318.map _
    FifthCompletedGlobal318.map.surjective
end FifthCompletedFinite318
