module
public import FifthQuarticCompletedMap318
public import ContactOverlapMaps318
public section
noncomputable section
namespace FifthSourceOverlap318
open Polynomial AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthQuarticCover318 FifthCharacterShortPolynomial318
set_option maxHeartbeats 750000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Overlap:=ContactKummerOrder318.OpenOrder units
abbrev Raw:=FifthCharacterField318.L
@[expose] def input:Quartic→ₐ[ℚ]Overlap where
  __ := (SourceOpenFractionField318.orderToOpen units).comp FifthCharacterSource318.toSource.toRingHom
  commutes' := RingHom.map_rat_algebraMap _
lemma input_parameter:input parameter=SourceInfinityOverlap318.t units:=by
  change SourceOpenFractionField318.orderToOpen units
    (FifthCharacterSource318.toSource (algebraMap ℚ[X] Quartic X))=_
  rw [AlgHom.commutes,SourceOpenFractionField318.orderToOpen_on_polynomial]
  rfl
lemma input_parameter_unit:IsUnit (input parameter):=by
  rw [input_parameter]
  exact SourceInfinityOverlap318.t_unit units
@[expose] def lift:FifthQuarticFinite318.Local→ₐ[ℚ]Overlap:=
  IsLocalization.Away.liftAlgHom parameter input_parameter_unit
lemma lift_on_order (r:Quartic):lift (algebraMap Quartic FifthQuarticFinite318.Local r)=input r:=
  IsLocalization.Away.lift_eq parameter input_parameter_unit r
lemma input_raw (r:Quartic):SourceOpenFractionField318.openEmbedding units (input r)=
    FifthCharacterSource318.toRaw r:=by
  change SourceOpenFractionField318.openEmbedding units
    (SourceOpenFractionField318.orderToOpen units (FifthCharacterSource318.toSource r))=_
  rw [SourceOpenFractionField318.openEmbedding_on_order,FifthCharacterSource318.toSource_embedding]
/-- Equality in the original entire overlap ring is tested through its proved
injective actual field embedding; this is not a geometric-point argument. -/
lemma lift_raw (r:FifthQuarticFinite318.Local):
    SourceOpenFractionField318.openEmbedding units (lift r)=
      (FifthQuarticFinite318.fieldEmbedding r:Raw):=by
  have h:(SourceOpenFractionField318.openEmbedding units).comp lift.toRingHom=
      FifthCharacterField318.field.subtype.comp FifthQuarticFinite318.fieldEmbedding:=by
    apply IsLocalization.ringHom_ext (Submonoid.powers parameter)
    apply RingHom.ext
    intro x
    change SourceOpenFractionField318.openEmbedding units
      (lift (algebraMap Quartic FifthQuarticFinite318.Local x))=
      (FifthQuarticFinite318.fieldEmbedding (algebraMap Quartic FifthQuarticFinite318.Local x):Raw)
    rw [lift_on_order,input_raw,FifthQuarticFinite318.fieldEmbedding_on_order]
    rfl
  exact RingHom.congr_fun h r
@[expose] def shortMap:ShortAffineJacobian318.Ring A B→ₐ[ℚ]Overlap:=
  lift.comp FifthQuarticFinite318.shortMap
lemma shortMap_raw (r:ShortAffineJacobian318.Ring A B):
    SourceOpenFractionField318.openEmbedding units (shortMap r)=
      (FifthShortFraction318.embedding r:Raw):=by
  change SourceOpenFractionField318.openEmbedding units (lift (FifthQuarticFinite318.shortMap r))=_
  rw [lift_raw,FifthQuarticFinite318.shortMap_field]
@[reassoc] lemma lift_square:
    Spec.map (CommRingCat.ofHom lift.toRingHom)≫cover.f false=
      Spec.map (CommRingCat.ofHom input.toRingHom):=by
  change Spec.map (CommRingCat.ofHom lift.toRingHom)≫
    Spec.map (CommRingCat.ofHom (algebraMap Quartic FifthQuarticFinite318.Local))=_
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact lift_on_order
/-- Exact restriction of the entire original finite-source map to the actual
source/infinity intersection, through the literal finite short target chart. -/
@[reassoc] theorem finite_restriction:
    ContactOverlapMaps318.sourceInclusion units≫FifthQuarticCompletedMap318.sourceMap=
      Spec.map (CommRingCat.ofHom shortMap.toRingHom)≫WeierstrassGluing318.finiteChart A B:=by
  rw [FifthQuarticCompletedMap318.sourceMap,←Category.assoc]
  have hi:ContactOverlapMaps318.sourceInclusion units≫FifthSourceAffine318.map=
      Spec.map (CommRingCat.ofHom input.toRingHom):=by
    change Spec.map (CommRingCat.ofHom (SourceOpenFractionField318.orderToOpen units))≫
      Spec.map (CommRingCat.ofHom FifthCharacterSource318.toSource.toRingHom)=_
    rw [←Spec.map_comp]
    rfl
  rw [hi,←lift_square,Category.assoc,FifthQuarticCompletedMap318.restriction]
  change Spec.map (CommRingCat.ofHom lift.toRingHom)≫
    (Spec.map (CommRingCat.ofHom FifthQuarticFinite318.shortMap.toRingHom)≫
      WeierstrassGluing318.finiteChart A B)=_
  rw [←Category.assoc,←Spec.map_comp]
  rfl
end FifthSourceOverlap318
