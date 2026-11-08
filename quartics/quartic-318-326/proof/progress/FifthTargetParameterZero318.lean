module
public import FifthTargetParameterRestriction318
public import FifthQuarticCompletedMap318
public import SpecSchematicDensity318
public import SchematicEqualityExtension318
public section
noncomputable section
namespace FifthTargetParameterZero318
open AlgebraicGeometry CategoryTheory Polynomial
open FifthCharacterShortPolynomial318 FifthQuarticCover318
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
@[expose] def finiteInclusion:Spec (CommRingCat.of FifthQuarticFinite318.Local)⟶Spec (CommRingCat.of Quartic):=
  Spec.map (CommRingCat.ofHom (algebraMap Quartic FifthQuarticFinite318.Local))
lemma finite_injective:Function.Injective (algebraMap Quartic FifthQuarticFinite318.Local):=by
  intro x y h
  apply FifthCharacterOrder318.embedding_injective
  rw [←FifthQuarticFinite318.fieldEmbedding_on_order,←FifthQuarticFinite318.fieldEmbedding_on_order]
  exact congrArg FifthQuarticFinite318.fieldEmbedding h
instance finite_dense:IsSchemeTheoreticallyDominant finiteInclusion:=
  SpecSchematicDensity318.spec_of_injective _ finite_injective
@[expose] def originalParameter:Spec (CommRingCat.of Quartic)⟶ProjectiveJLine318.scheme ℚ:=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval parameter).toRingHom)≫JLineAtlas318.chart ℚ 1
lemma originalParameter_over_Q:originalParameter≫ProjectiveJLine318.structureMap ℚ=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ Quartic)):=
  WeierstrassXStructure318.eval_over_base parameter 1
lemma finite_original:finiteInclusion≫originalParameter=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval FifthQuarticFiniteCoordinates318.t).toRingHom)≫JLineAtlas318.chart ℚ 1:=by
  rw [originalParameter,←Category.assoc,finiteInclusion,←Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro q
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C]
    exact (IsScalarTower.algebraMap_apply ℚ Quartic FifthQuarticFinite318.Local q).symm
  · simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X]
    rfl
/-- The whole quartic comparison, including its original branch, preserves
its actual original t-map. Schematic density is obtained from a proved injective ring map. -/
@[expose] def quarticMap:Spec (CommRingCat.of Quartic)⟶WeierstrassGluing318.scheme A B:=FifthQuarticCompletedMap318.map
@[reassoc] theorem quartic_over_t:quarticMap≫FifthTargetParameter318.map=originalParameter:=by
  have hQ:quarticMap≫WeierstrassGluing318.structureMap A B=Spec.map (CommRingCat.ofHom (algebraMap ℚ Quartic)):=FifthQuarticCompletedMap318.over_Q
  have hr:finiteInclusion≫quarticMap=Spec.map (CommRingCat.ofHom FifthQuarticFinite318.shortMap.toRingHom)≫WeierstrassGluing318.finiteChart A B:=FifthQuarticCompletedMap318.restriction false
  refine SchematicEqualityExtension318.ext (ProjectiveJLine318.structureMap ℚ) ?_ finiteInclusion ?_
  · rw [Category.assoc,FifthTargetParameter318.over_Q,hQ,originalParameter_over_Q]
  · rw [←Category.assoc,hr,Category.assoc,finite_original]
    change Spec.map (CommRingCat.ofHom FifthQuarticFinite318.shortMap.toRingHom)≫
      WeierstrassGluing318.finiteChart A B≫FifthTargetParameter318.map=_
    have h:=FifthTargetParameterRestriction318.finite_parameter FifthQuarticFinite318.shortMap
      FifthQuarticFiniteCoordinates318.t_unit.unit (by
        simpa only [FifthQuarticFiniteCoordinates318.t_unit.unit_spec] using FifthQuarticFiniteCoordinates318.x_relation)
    simpa only [FifthQuarticFiniteCoordinates318.t_unit.unit_spec] using h
/-- The chosen elliptic zero lies over the original t=0, not original quartic infinity. -/
@[reassoc] theorem zero_parameter:WeierstrassGluing318.infinity A B≫FifthTargetParameter318.map=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (0:ℚ)).toRingHom)≫JLineAtlas318.chart ℚ 1:=by
  have hb:FifthBranchScheme318.branch≫quarticMap=WeierstrassGluing318.infinity A B:=FifthQuarticCompletedMap318.branch_zero
  rw [←hb,Category.assoc,quartic_over_t]
  rw [originalParameter,←Category.assoc,FifthBranchScheme318.branch,←Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro q
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C,AlgHom.commutes]
  · simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X]
    simpa only [parameter,Polynomial.eval_X] using FifthBranchLocal318.origin_polynomial X
end FifthTargetParameterZero318
