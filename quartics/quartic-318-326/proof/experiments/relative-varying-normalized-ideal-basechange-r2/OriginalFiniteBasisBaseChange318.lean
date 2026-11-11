module
public import ScalarExtensionTensor318
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Dimension.Free

public section
noncomputable section
namespace OriginalFiniteBasisBaseChange318
open CategoryTheory
open scoped TensorProduct ChangeOfRings
universe u
variable {R A : Type u} [CommRing R] [Nontrivial R] [CommRing A] (f : R →+* A)
  (M : ModuleCat R) [Module.Finite R M] [Module.Free R M]

/-- Scalar extension of the ACTUAL old finite polynomial basis. The
coordinates are obtained from that basis's genuine tensor base change. -/
def coordinates : (ModuleCat.extendScalars f).obj M ≃ₗ[A]
    (Fin (Module.finrank R M) → A) := by
  letI := f.toAlgebra
  exact (ScalarExtensionTensor318.tensorEquiv M).trans
    ((Module.finBasis R M).baseChange A).equivFun

/-- The displayed coordinates retain the original scalar-extension unit and
original basis coefficients, including the reciprocal coefficient map. -/
lemma coordinates_tmul (a : A) (m : M) (i : Fin (Module.finrank R M)) :
    coordinates f M (a ⊗ₜ[R,f] m) i = f ((Module.finBasis R M).repr m i) * a := by
  letI := f.toAlgebra
  simp only [coordinates,LinearEquiv.trans_apply,ScalarExtensionTensor318.tensorEquiv_tmul,
    Module.Basis.equivFun_apply,Module.Basis.baseChange_repr_tmul,Algebra.smul_def,
    RingHom.algebraMap_toAlgebra]

lemma coordinates_unit (m : M) (i : Fin (Module.finrank R M)) :
    coordinates f M ((1 : A) ⊗ₜ[R,f] m) i = f ((Module.finBasis R M).repr m i) := by
  rw [coordinates_tmul,mul_one]

/-- Reindexing is only equality transport on an already proved rank equality. -/
def reindex {m n : ℕ} (h : m = n) : (Fin m → A) ≃ₗ[A] (Fin n → A) := by
  subst n
  exact LinearEquiv.refl _ _
end OriginalFiniteBasisBaseChange318
