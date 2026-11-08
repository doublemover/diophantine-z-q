module
public import FifthTargetParameter318
public import JLineOverlap318
public import FifthSourceInfinityAlgebra318
public section
noncomputable section
namespace FifthTargetParameterRestriction318
open AlgebraicGeometry CategoryTheory Polynomial
open FifthCharacterShortPolynomial318 FifthCharacterShortAlgebra318 FifthTargetParameter318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {S:Type} [CommRing S] [Algebra ℚ S]
lemma reciprocal_value (g:ShortAffineJacobian318.Ring A B→ₐ[ℚ]S):
    g reciprocalParameter=algebraMap ℚ S ((xScale⁻¹:ℚˣ):ℚ)*
      (g (ShortAffineJacobian318.x A B)-algebraMap ℚ S shift):=by
  simp only [reciprocalParameter,map_add,map_mul,g.commutes,map_neg]
  ring
lemma normalized_value (g:ShortAffineJacobian318.Ring A B→ₐ[ℚ]S) (u:S)
    (hx:g (ShortAffineJacobian318.x A B)=algebraMap ℚ S (xScale:ℚ)*u+algebraMap ℚ S shift):
    g reciprocalParameter=u:=by
  rw [reciprocal_value,hx,add_sub_cancel_right,←mul_assoc,←map_mul,Units.inv_mul,map_one,one_mul]
@[reassoc] theorem test_restriction (g:ShortAffineJacobian318.Ring A B→ₐ[ℚ]S):
    Spec.map (CommRingCat.ofHom g.toRingHom)≫WeierstrassGluing318.finiteChart A B≫map=
      Spec.map (CommRingCat.ofHom (Polynomial.aeval (g reciprocalParameter)).toRingHom)≫JLineAtlas318.chart ℚ 0:=by
  rw [finite_restriction,←Category.assoc,←Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro q
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C,g.commutes]
  · simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X]
@[reassoc] theorem normalized_restriction (g:ShortAffineJacobian318.Ring A B→ₐ[ℚ]S) (u:S)
    (hx:g (ShortAffineJacobian318.x A B)=algebraMap ℚ S (xScale:ℚ)*u+algebraMap ℚ S shift):
    Spec.map (CommRingCat.ofHom g.toRingHom)≫WeierstrassGluing318.finiteChart A B≫map=
      Spec.map (CommRingCat.ofHom (Polynomial.aeval u).toRingHom)≫JLineAtlas318.chart ℚ 0:=by
  rw [test_restriction,normalized_value g u hx]
/-- Exact original finite t-coordinate on every test algebra where t is a unit. -/
@[reassoc] theorem finite_parameter (g:ShortAffineJacobian318.Ring A B→ₐ[ℚ]S) (t:Sˣ)
    (hx:g (ShortAffineJacobian318.x A B)*(t:S)=algebraMap ℚ S (xScale:ℚ)+algebraMap ℚ S shift*(t:S)):
    Spec.map (CommRingCat.ofHom g.toRingHom)≫WeierstrassGluing318.finiteChart A B≫map=
      Spec.map (CommRingCat.ofHom (Polynomial.aeval (t:S)).toRingHom)≫JLineAtlas318.chart ℚ 1:=by
  have hc:g reciprocalParameter*(t:S)=1:=by
    rw [reciprocal_value]
    calc
      _=algebraMap ℚ S ((xScale⁻¹:ℚˣ):ℚ)*(g (ShortAffineJacobian318.x A B)*(t:S)-algebraMap ℚ S shift*(t:S)):=by ring
      _=1:=by rw [hx,add_sub_cancel_right,←map_mul,Units.inv_mul,map_one]
  have hi:g reciprocalParameter=(↑t⁻¹:S):=by
    calc
      _=g reciprocalParameter*((t:S)*↑t⁻¹):=by rw [Units.mul_inv,mul_one]
      _=(↑t⁻¹:S):=by rw [←mul_assoc,hc,one_mul]
  rw [test_restriction,hi]
  exact (JLineOverlap318.unit_chart_overlap (R:=ℚ) t).symm
/-- Whole reciprocal affine cubic has precisely its original u=1/t base map. -/
theorem cubic_restriction:
    Spec.map (CommRingCat.ofHom coordinateEquiv.symm.toRingHom)≫WeierstrassGluing318.finiteChart A B≫map=
      Spec.map (CommRingCat.ofHom (Polynomial.aeval FifthCharacterShortCoordinates318.u).toRingHom)≫JLineAtlas318.chart ℚ 0:=
  normalized_restriction coordinateEquiv.symm.toAlgHom _ FifthCharacterShortCoordinates318.inverse_x
/-- The entire original source infinity chart has its actual regular reciprocal t-coordinate. -/
theorem source_infinity_restriction:
    Spec.map (CommRingCat.ofHom FifthSourceInfinityAlgebra318.shortMap.toRingHom)≫
        WeierstrassGluing318.finiteChart A B≫map=
      Spec.map (CommRingCat.ofHom (Polynomial.aeval FifthSourceInfinityCoordinates318.u).toRingHom)≫JLineAtlas318.chart ℚ 0:=by
  apply normalized_restriction
  rw [FifthSourceInfinityAlgebra318.shortMap_x]
  rfl
end FifthTargetParameterRestriction318
