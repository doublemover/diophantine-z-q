module
public import Mathlib.Algebra.QuadraticAlgebra.BaseChange
public import Mathlib.Algebra.Algebra.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section
noncomputable section

namespace OriginalRCMilneSplitQuadratic318

open scoped TensorProduct

variable {F : Type*} [Field F] [CharZero F]

/-- Actual two evaluations at the chosen root and its conjugate.
The target is the product ALGEBRA, not the additive module K^2. -/
@[expose] def split (k s : F) (hs : s^2 = k) (hs0 : s ≠ 0) :
    QuadraticAlgebra F k 0 ≃ₐ[F] F × F where
  toFun z := (z.re+s*z.im,z.re-s*z.im)
  invFun z := ⟨(z.1+z.2)/2,(z.1-z.2)/(2*s)⟩
  left_inv z := by
    apply QuadraticAlgebra.ext
    · change ((z.re+s*z.im)+(z.re-s*z.im))/2 = z.re
      field_simp <;> ring
    · change ((z.re+s*z.im)-(z.re-s*z.im))/(2*s) = z.im
      field_simp [hs0] <;> ring
  right_inv z := by
    apply Prod.ext
    · change (z.1+z.2)/2+s*((z.1-z.2)/(2*s)) = z.1
      field_simp [hs0] <;> ring
    · change (z.1+z.2)/2-s*((z.1-z.2)/(2*s)) = z.2
      field_simp [hs0] <;> ring
  map_add' z w := by
    apply Prod.ext
    · change (z.re+w.re)+s*(z.im+w.im) = (z.re+s*z.im)+(w.re+s*w.im)
      ring
    · change (z.re+w.re)-s*(z.im+w.im) = (z.re-s*z.im)+(w.re-s*w.im)
      ring
  map_mul' z w := by
    apply Prod.ext
    · change (z*w).re+s*(z*w).im = (z.re+s*z.im)*(w.re+s*w.im)
      rw [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,← hs]
      ring
    · change (z*w).re-s*(z*w).im = (z.re-s*z.im)*(w.re-s*w.im)
      rw [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,← hs]
      ring
  commutes' a := by
    change (a+s*0,a-s*0)=(a,a)
    simp

@[simp] theorem split_apply (k s : F) (hs : s^2 = k) (hs0 : s ≠ 0)
    (z : QuadraticAlgebra F k 0) :
    split k s hs hs0 z=(z.re+s*z.im,z.re-s*z.im) := rfl

@[simp] theorem split_generator (k s : F) (hs : s^2 = k) (hs0 : s ≠ 0) :
    split k s hs hs0 QuadraticAlgebra.omega = (s,-s) := by
  simp [split_apply,QuadraticAlgebra.re_omega,QuadraticAlgebra.im_omega]

/-- The actual quadratic involution swaps the two ordered embeddings. -/
theorem split_star (k s : F) (hs : s^2 = k) (hs0 : s ≠ 0)
    (z : QuadraticAlgebra F k 0) :
    split k s hs hs0 (star z) =
      ((split k s hs hs0 z).2,(split k s hs hs0 z).1) := by
  simp only [split_apply,QuadraticAlgebra.re_star,QuadraticAlgebra.im_star]
  exact Prod.ext (by ring) (by ring)

theorem split_neg_root (k s : F) (hs : s^2 = k) (hs0 : s ≠ 0)
    (z : QuadraticAlgebra F k 0) :
    split k (-s) (by simpa only [neg_sq] using hs) (neg_ne_zero.mpr hs0) z =
      ((split k s hs hs0 z).2,(split k s hs hs0 z).1) := by
  simp only [split_apply]
  exact Prod.ext (by ring) (by ring)

@[expose] def changeZero {a b : F} (h : b = 0) :
    QuadraticAlgebra F a b ≃ₐ[F] QuadraticAlgebra F a 0 := by
  subst b
  exact AlgEquiv.refl

@[simp] theorem changeZero_generator {a b : F} (h : b = 0) :
    changeZero (a:=a) h QuadraticAlgebra.omega = QuadraticAlgebra.omega := by
  subst b
  rfl

variable {R : Type*} [CommRing R] [Algebra R F]

/-- The literal scalar extension of the chosen global quadratic
presentation. Specialize R=ℚ, k=k', F=ℚ_p. No integral split at 2. -/
@[expose] def splitBase (k : R) (s : F) (hs : s^2 = algebraMap R F k) (hs0 : s ≠ 0) :
    F ⊗[R] QuadraticAlgebra R k 0 ≃ₐ[F] F × F :=
  (QuadraticAlgebra.baseChangeEquiv F k 0).trans
    ((changeZero (a:=algebraMap R F k) (map_zero (algebraMap R F))).trans (split (algebraMap R F k) s hs hs0))

theorem splitBase_generator (k : R) (s : F) (hs : s^2 = algebraMap R F k) (hs0 : s ≠ 0) :
    splitBase k s hs hs0 (1 ⊗ₜ[R] QuadraticAlgebra.omega) = (s,-s) := by
  have hg : (QuadraticAlgebra.baseChangeEquiv F k 0)
      (1 ⊗ₜ[R] QuadraticAlgebra.omega) = QuadraticAlgebra.omega := by
    simp [QuadraticAlgebra.baseChangeEquiv_tmul]
  rw [splitBase,AlgEquiv.trans_apply,hg,AlgEquiv.trans_apply,
    changeZero_generator,split_generator]

end OriginalRCMilneSplitQuadratic318

#print axioms OriginalRCMilneSplitQuadratic318.splitBase_generator
#print axioms OriginalRCMilneSplitQuadratic318.split_star
