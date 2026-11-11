module
public import FourRootGluedScheme318
public import JLineOverlap318
public import ProjectiveAffineCharts318
public section
noncomputable section
namespace FourRootProjectiveProjection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open FourRootGluedScheme318 FourRootCoordinateOverlap318
variable (b:Fin 4→ℂ)
@[expose] def finiteCoordinate:Polynomial ℂ→ₐ[ℂ]Affine b:=
  Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none-algebraMap ℂ _ (b 0))
@[expose] def infinityCoordinate:Polynomial ℂ→ₐ[ℂ]Infinity b:=
  Polynomial.aeval (FourRootInfinityCoordinateRing318.coordinate b none^2)
@[expose] def finiteProjection:finiteScheme b⟶ProjectiveJLine318.scheme ℂ:=
  Spec.map (CommRingCat.ofHom (finiteCoordinate b).toRingHom)≫JLineAtlas318.chart ℂ 1
@[expose] def infinityProjection:infinityScheme b⟶ProjectiveJLine318.scheme ℂ:=
  Spec.map (CommRingCat.ofHom (infinityCoordinate b).toRingHom)≫JLineAtlas318.chart ℂ 0
@[expose] def overlapUnit:(InfinityOverlap b)ˣ where
  val:=ui b^2
  inv:=u b^2
  val_inv:=by rw [←mul_pow,mul_comm,u_ui];norm_num
  inv_val:=by rw [←mul_pow,u_ui];norm_num

lemma finite_coordinate_overlap:(toInfinityBase b).comp (finiteCoordinate b)=Polynomial.aeval (ui b^2):=by
  apply Polynomial.algHom_ext
  simp only [AlgHom.comp_apply,finiteCoordinate,Polynomial.aeval_X,map_sub,
    AlgHom.commutes,toInfinityBase_t]
  ring
lemma infinity_coordinate_overlap:
    (IsScalarTower.toAlgHom ℂ (Infinity b) (InfinityOverlap b)).comp (infinityCoordinate b)=
      Polynomial.aeval (u b^2):=by
  apply Polynomial.algHom_ext
  simp [infinityCoordinate,u]

/-- The reciprocal chart is based at t-b0. Its exact coordinate u² is
regular at every one of the eight infinity points. -/
lemma projection_overlap:intoFinite b≫finiteProjection b=intoInfinity b≫infinityProjection b:=by
  rw [intoFinite_eq]
  unfold finiteProjection infinityProjection intoInfinity
  rw [←Category.assoc,←Spec.map_comp,←Category.assoc,←Spec.map_comp]
  have hf:=congrArg (fun f:Polynomial ℂ→ₐ[ℂ]InfinityOverlap b=>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (finite_coordinate_overlap b)
  have hi:=congrArg (fun f:Polynomial ℂ→ₐ[ℂ]InfinityOverlap b=>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (infinity_coordinate_overlap b)
  rw [hf,hi]
  exact JLineOverlap318.unit_chart_overlap (R:=ℂ) (overlapUnit b)

@[expose] def centeredProjection:scheme b⟶ProjectiveJLine318.scheme ℂ:=
  pushout.desc (finiteProjection b) (infinityProjection b) (projection_overlap b)
@[reassoc,simp] lemma finite_centered:finiteChart b≫centeredProjection b=finiteProjection b:=pushout.inl_desc ..
@[reassoc,simp] lemma infinity_centered:infinityChart b≫centeredProjection b=infinityProjection b:=pushout.inr_desc ..

/-- The specified affine translation restores EXACTLY the original t,
not a silently shifted projective coordinate. This is a genuine Scheme
map, regular also at every normalized infinity point. -/
@[expose] def projection:scheme b⟶ProjectiveJLine318.scheme ℂ:=
  centeredProjection b≫ProjectiveAffineLine318.map ℂ 1 (b 0)
@[reassoc] theorem finite_projection:finiteChart b≫projection b=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval
      (FourRootAffineCoordinateRing318.coordinate b none)).toRingHom)≫JLineAtlas318.chart ℂ 1:=by
  rw [projection,finite_centered_assoc]
  unfold finiteProjection
  rw [Category.assoc,ProjectiveAffineCharts318.chart_naturality,←Category.assoc,←Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c;simp [finiteCoordinate]
  · simp [finiteCoordinate]
@[reassoc] theorem infinity_projection:infinityChart b≫projection b=
    Spec.map (CommRingCat.ofHom (infinityCoordinate b).toRingHom)≫JLineAtlas318.chart ℂ 0≫
      ProjectiveAffineLine318.map ℂ 1 (b 0):=by
  rw [projection,infinity_centered_assoc]
  rfl

theorem over_base:projection b≫ProjectiveJLine318.structureMap ℂ=structureMap b:=by
  rw [projection,Category.assoc,ProjectiveAffineCharts318.map_over_base]
  apply FourRootGluedScheme318.hom_ext
  · rw [finite_centered_assoc,finite_structure]
    unfold finiteProjection
    rw [Category.assoc,JLineAtlas318.chart_over_base,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact (finiteCoordinate b).commutes c
  · rw [infinity_centered_assoc,infinity_structure]
    unfold infinityProjection
    rw [Category.assoc,JLineAtlas318.chart_over_base,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact (infinityCoordinate b).commutes c
end FourRootProjectiveProjection318
