module
public import OriginalSparseGluedScheme318
public import OriginalSparseP1Overlap318

/-! The genuine cover to the literal standard projective line. -/
public section
noncomputable section
namespace OriginalSparseP1Projection318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open OriginalSparseGluedScheme318 OriginalSparseQuadraticCharts318
universe u
variable {R : Type u} [CommRing R] (s t : R)

@[expose] def finiteCoordinate : R[X] →ₐ[R] CF s t := aeval (x (F s t))
@[expose] def infinityCoordinate : R[X] →ₐ[R] CG s t := aeval (x (G s t))

@[expose] def finiteProjection : finiteScheme s t ⟶ ProjectiveJLine318.scheme R :=
  Spec.map (CommRingCat.ofHom (finiteCoordinate s t).toRingHom) ≫ JLineAtlas318.chart R 1
@[expose] def infinityProjection : infinityScheme s t ⟶ ProjectiveJLine318.scheme R :=
  Spec.map (CommRingCat.ofHom (infinityCoordinate s t).toRingHom) ≫ JLineAtlas318.chart R 0

@[expose] def overlapUnit : (LG s t)ˣ where
  val := xi (G s t)
  inv := xx (G s t)
  val_inv := xi_xx _
  inv_val := xx_xi _

lemma finite_coordinate_overlap :
    (finToInfBase s t).comp (finiteCoordinate s t)=aeval (xi (G s t)) := by
  apply Polynomial.algHom_ext
  simp [finiteCoordinate]
lemma infinity_coordinate_overlap :
    (IsScalarTower.toAlgHom R (CG s t) (LG s t)).comp (infinityCoordinate s t)=
      aeval (xx (G s t)) := by
  apply Polynomial.algHom_ext
  simp [infinityCoordinate,xx]

lemma projection_overlap : intoFinite s t ≫ finiteProjection s t =
    intoInfinity s t ≫ infinityProjection s t := by
  rw [intoFinite_eq]
  unfold finiteProjection infinityProjection intoInfinity
  rw [←Category.assoc,←Spec.map_comp,←Category.assoc,←Spec.map_comp]
  have hf := congrArg (fun f : R[X] →ₐ[R] LG s t =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (finite_coordinate_overlap s t)
  have hi := congrArg (fun f : R[X] →ₐ[R] LG s t =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (infinity_coordinate_overlap s t)
  change Spec.map (CommRingCat.ofHom ((finToInfBase s t).comp (finiteCoordinate s t)).toRingHom) ≫ _ =
    Spec.map (CommRingCat.ofHom ((IsScalarTower.toAlgHom R (CG s t) (LG s t)).comp
      (infinityCoordinate s t)).toRingHom) ≫ _
  rw [hf,hi]
  exact OriginalSparseP1Overlap318.unit_chart_overlap (R:=R) (overlapUnit s t)

@[expose] def projection : scheme s t ⟶ ProjectiveJLine318.scheme R :=
  pushout.desc (finiteProjection s t) (infinityProjection s t) (projection_overlap s t)
@[reassoc,simp] lemma finite_projection : finiteChart s t ≫ projection s t=finiteProjection s t :=
  pushout.inl_desc ..
@[reassoc,simp] lemma infinity_projection : infinityChart s t ≫ projection s t=infinityProjection s t :=
  pushout.inr_desc ..

theorem over_base : projection s t ≫ ProjectiveJLine318.structureMap R=structureMap s t := by
  apply OriginalSparseGluedScheme318.hom_ext
  · rw [finite_projection_assoc,finite_structure]
    unfold finiteProjection
    rw [Category.assoc,JLineAtlas318.chart_over_base,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact (finiteCoordinate s t).commutes c
  · rw [infinity_projection_assoc,infinity_structure]
    unfold infinityProjection
    rw [Category.assoc,JLineAtlas318.chart_over_base,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact (infinityCoordinate s t).commutes c

end OriginalSparseP1Projection318
