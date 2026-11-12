module
public import WeierstrassActualInfinityProjection318
public import ProjectiveLineActualAutomorphismPoints318
public section
noncomputable section
namespace WeierstrassInfinityPointProjection318
open AlgebraicGeometry CategoryTheory Polynomial
open ProjectiveLineComplexSchemePoints318 ProjectiveLineActualAutomorphismPoints318
open WeierstrassReciprocalCoordinate318 WeierstrassReciprocalOverlap318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every literal native-chart solution evaluates the ACTUAL infinity
coordinate ring, including the origin. -/
@[expose] def evaluation (A B u v : ℂ) (he:v-u^3-A*u*v^2-B*v^3=0) :
    InfinityChart318.Ring A B →ₐ[ℂ] ℂ := by
  let e : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ := MvPolynomial.aeval ![u,v]
  have hk : Ideal.span (Set.range (InfinityChart318.equations A B)) ≤ RingHom.ker e.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨_,rfl⟩
    change e (InfinityChart318.equation A B)=0
    simpa [e,InfinityChart318.equation] using he
  exact Ideal.Quotient.liftₐ _ e (fun f hf=>hk hf)
lemma evaluation_x (A B u v : ℂ) (he) :
    evaluation A B u v he (InfinityChart318.x A B)=u := by
  simp [evaluation,InfinityChart318.x,Ideal.Quotient.liftₐ_apply]
lemma evaluation_z (A B u v : ℂ) (he) :
    evaluation A B u v he (InfinityChart318.z A B)=v := by
  simp [evaluation,InfinityChart318.z,Ideal.Quotient.liftₐ_apply]
lemma evaluation_denominator (A B u v : ℂ) (he) :
    evaluation A B u v he (denominator A B)=1-A*u*v-B*v^2 := by
  simp only [denominator,map_sub,map_one,map_mul,map_pow,AlgHom.commutes,
    evaluation_x,evaluation_z]

@[expose] def point (A B u v : ℂ) (he:v-u^3-A*u*v^2-B*v^3=0) :=
  Spec.map (CommRingCat.ofHom (evaluation A B u v he).toRingHom) ≫
    WeierstrassGluing318.infinityChart A B

@[expose] def nearEvaluation (A B u v : ℂ) (he:v-u^3-A*u*v^2-B*v^3=0)
    (hD:1-A*u*v-B*v^2≠0) : Near A B →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom (f:=evaluation A B u v he) (denominator A B)
    (by rw [evaluation_denominator]; exact isUnit_iff_ne_zero.mpr hD)
lemma nearEvaluation_base (A B u v : ℂ) (he) (hD) (a:I A B) :
    nearEvaluation A B u v he hD (algebraMap (I A B) (Near A B) a)=
      evaluation A B u v he a := IsLocalization.Away.lift_eq _ _ a
lemma nearEvaluation_inverse (A B u v : ℂ) (he) (hD) :
    nearEvaluation A B u v he hD (inverseD A B)=(1-A*u*v-B*v^2)⁻¹ := by
  have hh:=congrArg (nearEvaluation A B u v he hD)
    (IsLocalization.Away.mul_invSelf (S:=Near A B) (denominator A B))
  rw [map_mul,map_one,nearEvaluation_base,evaluation_denominator] at hh
  apply (mul_left_cancel₀ hD)
  exact hh.trans (mul_inv_cancel₀ hD).symm
lemma nearEvaluation_reciprocal (A B u v : ℂ) (he) (hD) :
    nearEvaluation A B u v he hD (reciprocal A B)=u^2/(1-A*u*v-B*v^2) := by
  rw [reciprocal,map_mul,map_pow,nearEvaluation_inverse]
  have hx : nearEvaluation A B u v he hD (x A B)=u := by
    rw [x,nearEvaluation_base,evaluation_x]
  rw [hx,div_eq_mul_inv]
lemma nearEvaluation_factor (A B u v : ℂ) (he) (hD) :
    Spec.map (CommRingCat.ofHom (nearEvaluation A B u v he hD).toRingHom) ≫ nearBase A B=
      Spec.map (CommRingCat.ofHom (evaluation A B u v he).toRingHom) := by
  unfold nearBase
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact nearEvaluation_base A B u v he hD

/-- The actual full native projection on every point of the reciprocal
neighborhood. This is a Scheme-morphism equality, not just a rational
function identity away from the infinity point. -/
theorem native_projection (A B u v : ℂ) (he:v-u^3-A*u*v^2-B*v^3=0)
    (hD:1-A*u*v-B*v^2≠0) :
    point A B u v he ≫ WeierstrassXProjection318.xMap A B=
      (chartPoint 0 (u^2/(1-A*u*v-B*v^2))).val := by
  rw [point,Category.assoc,WeierstrassXProjection318.infinityChart_xMap,
    ←nearEvaluation_factor A B u v he hD,Category.assoc,
    WeierstrassXProjection318.infinityProjection_near]
  unfold nearProjection
  rw [←Category.assoc,←Spec.map_comp]
  change Spec.map _ ≫ JLineAtlas318.chart ℂ 0=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (u^2/(1-A*u*v-B*v^2))).toRingHom) ≫ _
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.coe_toRingHom,Polynomial.aeval_C,AlgHom.commutes]
  · simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.coe_toRingHom,Polynomial.aeval_X,nearEvaluation_reciprocal]

/-- True reciprocal-chart action of a translation. The zero case is the
actual infinity point and is retained, not removed by cancellation. -/
theorem translated_reciprocal (r s:ℂ) (hs:1+s*r≠0) :
    (chartPoint 0 r).val ≫ (ProjectiveAffineLine318.iso ℂ 1 s).hom=
      (chartPoint 0 (r/(1+s*r))).val := by
  by_cases hr:r=0
  · subst r
    simpa using affine_infinity (1:ℂˣ) s
  · have ho : (chartPoint 1 r⁻¹).val=(chartPoint 0 r).val := by
      simpa only [inv_inv] using congrArg Subtype.val (reciprocal_overlap r⁻¹ (inv_ne_zero hr))
    have hz:r⁻¹+s≠0 := by
      intro hz
      apply hs
      calc
        1+s*r=(r⁻¹+s)*r := by field_simp [hr];ring
        _=0 := by rw [hz,zero_mul]
    rw [←ho,affine_finite]
    simp only [Units.val_one,one_mul]
    rw [congrArg Subtype.val (reciprocal_overlap (r⁻¹+s) hz)]
    congr 2
    field_simp [hr,hs,hz]
    <;> ring
end WeierstrassInfinityPointProjection318
