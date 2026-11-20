module
public import ChartNegation318
public section
noncomputable section
open ShortAffineJacobian318 AffineEquationFunctor318

namespace SelectedShortAffineScaling318
variable {R : Type*} [CommRing R]
variable (A B C D : R) (u : Rˣ)
variable (hA : A = (u:R)^4*C) (hB : B = (u:R)^6*D)

/-- Contravariant coordinate map of the actual short affine equations:
the geometric point map goes from (C,D) to (A,B). -/
@[expose] def hom : Ring A B →ₐ[R] Ring C D :=
  toHom A B ⟨(algebraMap R (Ring C D) (u:R)^2*x C D,
    algebraMap R (Ring C D) (u:R)^3*y C D),by
      rw [hA,hB]
      simp only [map_mul,map_pow]
      linear_combination (algebraMap R (Ring C D) (u:R))^6*relation C D⟩

@[simp] theorem hom_x :
    hom A B C D u hA hB (x A B) = algebraMap R (Ring C D) (u:R)^2*x C D :=
  toHom_x ..
@[simp] theorem hom_y :
    hom A B C D u hA hB (y A B) = algebraMap R (Ring C D) (u:R)^3*y C D :=
  toHom_y ..

private theorem inv_pow_mul {S : Type*} [CommRing S] [Algebra R S]
    (v : Rˣ) (n : ℕ) (z : S) :
    (algebraMap R S (↑v⁻¹:R))^n * ((algebraMap R S (v:R))^n * z) = z := by
  rw [←mul_assoc,←mul_pow,←map_mul,Units.inv_mul,map_one,one_pow,one_mul]

private theorem pow_inv_mul {S : Type*} [CommRing S] [Algebra R S]
    (v : Rˣ) (n : ℕ) (z : S) :
    (algebraMap R S (v:R))^n * ((algebraMap R S (↑v⁻¹:R))^n * z) = z := by
  rw [←mul_assoc,←mul_pow,←map_mul,Units.mul_inv,map_one,one_pow,one_mul]

private theorem inverse_coeff (v : Rˣ) (n : ℕ) (s t : R) (h : s=(v:R)^n*t) :
    t=(↑v⁻¹:R)^n*s := by
  rw [h,←mul_assoc,←mul_pow,Units.inv_mul,one_pow,one_mul]

/-- Over arbitrary test rings this is an isomorphism, not only a
bijection on fields. Its inverse uses the same unit with inverse scale. -/
@[expose] def equiv : Ring A B ≃ₐ[R] Ring C D :=
  AlgEquiv.ofAlgHom (hom A B C D u hA hB)
    (hom C D A B u⁻¹ (inverse_coeff u 4 A C hA) (inverse_coeff u 6 B D hB))
    (by
      apply hom_ext
      · simpa only [AlgHom.comp_apply,hom_x,map_mul,map_pow,AlgHom.commutes,AlgHom.id_apply]
          using inv_pow_mul u 2 (x C D)
      · simpa only [AlgHom.comp_apply,hom_y,map_mul,map_pow,AlgHom.commutes,AlgHom.id_apply]
          using inv_pow_mul u 3 (y C D))
    (by
      apply hom_ext
      · simpa only [AlgHom.comp_apply,hom_x,map_mul,map_pow,AlgHom.commutes,AlgHom.id_apply]
          using pow_inv_mul u 2 (x A B)
      · simpa only [AlgHom.comp_apply,hom_y,map_mul,map_pow,AlgHom.commutes,AlgHom.id_apply]
          using pow_inv_mul u 3 (y A B))

/-- The map is the actual pullback of coordinates of affine sections. -/
theorem point_coordinates {S : Type*} [CommRing S] [Algebra R S]
    (P : Ring C D →ₐ[R] S) :
    ((ofHom A B (P.comp (hom A B C D u hA hB))).val : S × S) =
      (algebraMap R S (u:R)^2 * P (x C D),algebraMap R S (u:R)^3 * P (y C D)) := by
  change (P (hom A B C D u hA hB (x A B)),P (hom A B C D u hA hB (y A B))) = _
  simp only [hom_x,hom_y,map_mul,map_pow,AlgHom.commutes]

/-- Changing the square root flips the actual target negation morphism,
not a sign relation only on geometric points. -/
theorem hom_neg_scale (ha : A = (↑(-u):R)^4*C) (hb : B = (↑(-u):R)^6*D) :
    hom A B C D (-u) ha hb =
      (hom A B C D u hA hB).comp (ChartNegation318.affineNeg A B) := by
  apply hom_ext
  · simp only [hom_x,AlgHom.comp_apply,ChartNegation318.affineNeg_x,Units.val_neg,map_neg]
    ring
  · simp only [hom_y,AlgHom.comp_apply,ChartNegation318.affineNeg_y,Units.val_neg,map_neg]
    ring

/-- Equivariance with the two actual negation endomorphisms. -/
theorem hom_commutes_neg :
    (ChartNegation318.affineNeg C D).comp (hom A B C D u hA hB) =
      (hom A B C D u hA hB).comp (ChartNegation318.affineNeg A B) := by
  apply hom_ext
  · simp only [hom_x,AlgHom.comp_apply,ChartNegation318.affineNeg_x,map_mul,map_pow,
      AlgHom.commutes]
  · simp only [hom_y,AlgHom.comp_apply,ChartNegation318.affineNeg_y,map_mul,map_pow,
      AlgHom.commutes,map_neg]
    ring

/-- Both overlap branches restrict to the SAME map on every actual
negation-fixed element of the target coordinate algebra. -/
theorem hom_same_on_fixed (ha : A = (↑(-u):R)^4*C) (hb : B = (↑(-u):R)^6*D)
    (z : Ring A B) (hz : ChartNegation318.affineNeg A B z = z) :
    hom A B C D (-u) ha hb z = hom A B C D u hA hB z := by
  rw [hom_neg_scale A B C D u hA hB ha hb,AlgHom.comp_apply,hz]

end SelectedShortAffineScaling318

#print axioms SelectedShortAffineScaling318.equiv
#print axioms SelectedShortAffineScaling318.hom_same_on_fixed
