module
public import IntegralWholeSignedSourceRoots318
public section
noncomputable section
namespace LocalizedTensorRestriction318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A L B T : Type*} [CommRing A] [CommRing L] [CommRing B] [CommRing T]
variable [Algebra A L] [Algebra A B] (x : A) [IsLocalization.Away x L]
variable (f : B →+* T) (h : IsUnit (f (algebraMap A B x)))
@[expose, instance_reducible] def targetAlgebra : Algebra A T := (f.comp (algebraMap A B)).toAlgebra

@[expose] def baseMap : letI : Algebra A T := targetAlgebra (A := A) f; L →ₐ[A] T := by
  letI : Algebra A T := targetAlgebra (A := A) f
  exact {
    __ := IsLocalization.Away.lift (g := f.comp (algebraMap A B)) x h
    commutes' a := IsLocalization.Away.lift_eq (g := f.comp (algebraMap A B)) (hg := h) x a }
@[expose] def rightMap : letI : Algebra A T := targetAlgebra (A := A) f; B →ₐ[A] T := by
  letI : Algebra A T := targetAlgebra (A := A) f
  exact { __ := f, commutes' _ := rfl }

/-- The actual tensor-localization universal map. The only invertibility
input is the image of the same original element being localized. -/
@[expose] def lift : L ⊗[A] B →+* T := by
  letI : Algebra A T := targetAlgebra (A := A) f
  exact (Algebra.TensorProduct.lift (baseMap x f h) (rightMap f)
    (fun _ _ => Commute.all _ _)).toRingHom

@[simp] theorem lift_right (b : B) : lift x f h (1 ⊗ₜ[A] b)=f b := by
  letI : Algebra A T := targetAlgebra (A := A) f
  simp only [lift,Algebra.TensorProduct.lift_tmul,map_one,one_mul] <;> rfl
@[simp] theorem lift_left (a : A) :
    lift x f h ((algebraMap A L a) ⊗ₜ[A] (1:B))=f (algebraMap A B a) := by
  letI : Algebra A T := targetAlgebra (A := A) f
  simp only [lift,Algebra.TensorProduct.lift_tmul,map_one,mul_one]
  exact IsLocalization.Away.lift_eq (g := f.comp (algebraMap A B)) (hg := h) x a
end LocalizedTensorRestriction318
