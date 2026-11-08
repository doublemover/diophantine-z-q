module
public import AffineEquationFunctor318
public section
noncomputable section
namespace AffineRationalScaling318
open ShortAffineJacobian318 AffineEquationFunctor318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A B C D:ℚ) (u:ℚˣ) (hA:A=(u:ℚ)^4*C) (hB:B=(u:ℚ)^6*D)

@[expose] def hom : Ring A B→ₐ[ℚ]Ring C D:=
  toHom A B ⟨(algebraMap ℚ (Ring C D) (u:ℚ)^2*x C D,
    algebraMap ℚ (Ring C D) (u:ℚ)^3*y C D),by
      rw [hA,hB]
      simp only [map_mul,map_pow]
      linear_combination (algebraMap ℚ (Ring C D) (u:ℚ))^6*relation C D⟩
@[simp] lemma hom_x : hom A B C D u hA hB (x A B)=
    algebraMap ℚ (Ring C D) (u:ℚ)^2*x C D:=toHom_x ..
@[simp] lemma hom_y : hom A B C D u hA hB (y A B)=
    algebraMap ℚ (Ring C D) (u:ℚ)^3*y C D:=toHom_y ..

include hA in
lemma inverse_A : C=(↑u⁻¹:ℚ)^4*A:=by
  rw [hA]
  simp only [Units.val_inv_eq_inv_val]
  field_simp
include hB in
lemma inverse_B : D=(↑u⁻¹:ℚ)^6*B:=by
  rw [hB]
  simp only [Units.val_inv_eq_inv_val]
  field_simp

lemma map_inv_pow_mul {S:Type*} [CommRing S] [Algebra ℚ S] (u:ℚˣ) (n:ℕ) (x:S) :
    (algebraMap ℚ S (↑u⁻¹:ℚ))^n*((algebraMap ℚ S (u:ℚ))^n*x)=x:=by
  rw [←mul_assoc,←mul_pow,←map_mul,Units.inv_mul,map_one,one_pow,one_mul]
lemma map_pow_inv_mul {S:Type*} [CommRing S] [Algebra ℚ S] (u:ℚˣ) (n:ℕ) (x:S) :
    (algebraMap ℚ S (u:ℚ))^n*((algebraMap ℚ S (↑u⁻¹:ℚ))^n*x)=x:=by
  rw [←mul_assoc,←mul_pow,←map_mul,Units.mul_inv,map_one,one_pow,one_mul]

/-- Literal inverse coordinate maps on the actual affine Weierstrass
coordinate algebras, preserving the specified rational scalar map. -/
@[expose] def equiv : Ring A B≃ₐ[ℚ]Ring C D:=
  AlgEquiv.ofAlgHom (hom A B C D u hA hB)
    (hom C D A B u⁻¹ (inverse_A A C u hA) (inverse_B B D u hB))
    (by
      apply hom_ext
      · simpa only [AlgHom.comp_apply,hom_x,map_mul,map_pow,AlgHom.commutes,AlgHom.id_apply] using
          map_inv_pow_mul u 2 (x C D)
      · simpa only [AlgHom.comp_apply,hom_y,map_mul,map_pow,AlgHom.commutes,AlgHom.id_apply] using
          map_inv_pow_mul u 3 (y C D))
    (by
      apply hom_ext
      · simpa only [AlgHom.comp_apply,hom_x,map_mul,map_pow,AlgHom.commutes,AlgHom.id_apply] using
          map_pow_inv_mul u 2 (x A B)
      · simpa only [AlgHom.comp_apply,hom_y,map_mul,map_pow,AlgHom.commutes,AlgHom.id_apply] using
          map_pow_inv_mul u 3 (y A B))
end AffineRationalScaling318
