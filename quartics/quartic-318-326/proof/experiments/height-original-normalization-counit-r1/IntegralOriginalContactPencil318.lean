module
public import IntegralWholePencilMap318
public section
noncomputable section
namespace IntegralOriginalContactPencil318
open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralSourceBranches318 IntegralWholeFiniteComparison318 IntegralPencilScalarMaps318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)

/-- The original contact t morphism on the ACTUAL old integral model,
transported through its explicit signed-root scheme isomorphism. -/
@[expose] def projection : IntegralGluedModel318.scheme R c ⟶ ProjectiveJLine318.scheme R :=
  IntegralOriginalModelMorphism318.map R c ≫ IntegralWholePencilMap318.projection R c

@[expose] def infinityRatioValue : IntegralInfinityChart318.Order R c :=
  IntegralInfinityCoefficients318.k0 R c * IntegralInfinityChart318.coordinate R c ^ 2

theorem finite_polynomial :
    (comparison R c).symm.toRingHom.comp (finiteCoordinate R c).toRingHom=
      algebraMap R[X] (SourceOrder R c) := by
  apply Polynomial.ringHom_ext
  · intro r
    change (comparison R c).symm (finiteCoordinate R c (C r))=_
    rw [finiteCoordinate,Polynomial.aeval_C,AlgEquiv.commutes]
    rfl
  · change (comparison R c).symm (finiteCoordinate R c X)=_
    apply (comparison R c).injective
    rw [AlgEquiv.apply_symm_apply,comparison_t,finiteCoordinate,Polynomial.aeval_X,map_mul,map_pow]
    rfl

theorem infinity_polynomial :
    (IntegralOriginalInfinityEmbedding318.ringMap R c).comp (reciprocalCoordinate R c).toRingHom=
      (Polynomial.aeval (R:=R) (infinityRatioValue R c)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change IntegralOriginalInfinityEmbedding318.ringMap R c (reciprocalCoordinate R c (C r))=_
    rw [reciprocalCoordinate,Polynomial.aeval_C]
    change IntegralOriginalInfinityEmbedding318.ringMap R c
      (algebraMap R[X] (IntegralWholeReciprocalOrders318.InfinityOrder R c) (C r))=_
    rw [IntegralOriginalInfinityEmbedding318.polynomial,Polynomial.aeval_C]
    rfl
  · change IntegralOriginalInfinityEmbedding318.ringMap R c (reciprocalCoordinate R c X)=_
    rw [reciprocalCoordinate,Polynomial.aeval_X,map_mul,map_pow]
    change IntegralOriginalInfinityEmbedding318.ringMap R c
      (algebraMap R[X] (IntegralWholeReciprocalOrders318.InfinityOrder R c) (C (↑(c 0)⁻¹:R))) *
      (IntegralOriginalInfinityEmbedding318.ringMap R c
        (algebraMap R[X] (IntegralWholeReciprocalOrders318.InfinityOrder R c) X))^2=_
    rw [IntegralOriginalInfinityEmbedding318.polynomial,
      IntegralOriginalInfinityEmbedding318.polynomial,Polynomial.aeval_X]
    rfl

/-- On the original whole finite source this is exactly its original
polynomial t structure map. -/
theorem finite_restriction : IntegralGluedModel318.finiteChart R c ≫ projection R c=
    Spec.map (CommRingCat.ofHom (algebraMap R[X] (SourceOrder R c))) ≫ JLineAtlas318.chart R 1 := by
  rw [projection,←Category.assoc,IntegralOriginalModelMorphism318.finiteChart_map]
  unfold IntegralWholeReciprocalGluing318.originalSourceChart
  rw [Category.assoc,IntegralWholePencilMap318.finite_restriction,
    IntegralWholePencilMap318.finiteProjection,←Category.assoc,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((comparison R c).symm.toRingHom.comp (finiteCoordinate R c).toRingHom)) ≫ _ = _
  rw [finite_polynomial]

theorem infinity_restriction : IntegralGluedModel318.infinityChart R c ≫ projection R c=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R) (infinityRatioValue R c)).toRingHom) ≫
      JLineAtlas318.chart R 0 := by
  rw [projection,←Category.assoc,IntegralOriginalModelMorphism318.infinityChart_map]
  unfold IntegralOriginalInfinityEmbedding318.chart
  rw [Category.assoc,IntegralWholePencilMap318.reciprocal_restriction,
    IntegralWholePencilMap318.reciprocalProjection,←Category.assoc]
  unfold IntegralOriginalInfinityEmbedding318.inclusion
  rw [←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((IntegralOriginalInfinityEmbedding318.ringMap R c).comp (reciprocalCoordinate R c).toRingHom)) ≫ _ = _
  rw [infinity_polynomial]

/-- The original coefficient-ring structure is unchanged by the pencil. -/
theorem over_base : projection R c ≫ ProjectiveJLine318.structureMap R=
    IntegralGluedModel318.structureMap R c := by
  apply pushout.hom_ext
  · rw [←Category.assoc,finite_restriction,Category.assoc,JLineAtlas318.chart_over_base,
      IntegralGluedModel318.finiteChart_structure,←Spec.map_comp]
    congr 1
  · rw [←Category.assoc,infinity_restriction,Category.assoc,JLineAtlas318.chart_over_base,
      IntegralGluedModel318.infinityChart_structure,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact (Polynomial.aeval (R:=R) (infinityRatioValue R c)).commutes
end IntegralOriginalContactPencil318
