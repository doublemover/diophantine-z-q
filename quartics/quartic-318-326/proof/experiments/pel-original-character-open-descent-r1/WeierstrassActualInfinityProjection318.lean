module
public import WeierstrassXProjection318
public import ProjectiveLineComplexSchemePoints318
public section
noncomputable section
namespace WeierstrassActualInfinityProjection318
open AlgebraicGeometry CategoryTheory Polynomial
open WeierstrassReciprocalCoordinate318 WeierstrassReciprocalOverlap318
open ProjectiveLineComplexSchemePoints318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A B:ℂ)

lemma origin_denominator : InfinityChart318.origin A B (denominator A B)=1 := by
  simp only [denominator,map_sub,map_one,map_mul,map_pow,AlgHom.commutes,
    InfinityChart318.origin_x,InfinityChart318.origin_z,mul_zero,zero_pow (by decide : 2≠0),
    sub_zero]

/-- The actual infinity section factors through the reciprocal x
neighborhood because its defining denominator evaluates to ONE. -/
@[expose] def nearOrigin : Near A B →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom (f:=InfinityChart318.origin A B) (denominator A B)
    (by rw [origin_denominator]; exact isUnit_one)

lemma nearOrigin_on_base (a:I A B) :
    nearOrigin A B (algebraMap (I A B) (Near A B) a)=InfinityChart318.origin A B a :=
  IsLocalization.Away.lift_eq _ _ a

lemma nearOrigin_reciprocal : nearOrigin A B (reciprocal A B)=0 := by
  rw [reciprocal,map_mul,map_pow]
  have hx : nearOrigin A B (x A B)=0 := by
    rw [x,nearOrigin_on_base,InfinityChart318.origin_x]
  rw [hx,zero_pow (by decide : 2≠0),zero_mul]

lemma nearOrigin_factor :
    Spec.map (CommRingCat.ofHom (nearOrigin A B).toRingHom) ≫ nearBase A B=
      InfinitySmooth318.infinity A B := by
  unfold nearBase InfinitySmooth318.infinity
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact nearOrigin_on_base A B

/-- The whole original completed Weierstrass x projection sends its
actual infinity section to the actual projective infinity Scheme point.
This is proved in the reciprocal chart, not inferred from a pole slogan. -/
theorem infinity_projection :
    WeierstrassGluing318.infinity A B ≫ WeierstrassXProjection318.xMap A B=
      (chartPoint 0 0).val := by
  change (InfinitySmooth318.infinity A B ≫ WeierstrassGluing318.infinityChart A B) ≫ _=_
  rw [Category.assoc,WeierstrassXProjection318.infinityChart_xMap,
    ←nearOrigin_factor A B,Category.assoc,WeierstrassXProjection318.infinityProjection_near]
  unfold nearProjection
  rw [←Category.assoc,←Spec.map_comp]
  change Spec.map _ ≫ JLineAtlas318.chart ℂ 0=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (0:ℂ)).toRingHom) ≫ JLineAtlas318.chart ℂ 0
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.coe_toRingHom,Polynomial.aeval_C,AlgHom.commutes]
  · simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.coe_toRingHom,Polynomial.aeval_X,nearOrigin_reciprocal]
end WeierstrassActualInfinityProjection318
