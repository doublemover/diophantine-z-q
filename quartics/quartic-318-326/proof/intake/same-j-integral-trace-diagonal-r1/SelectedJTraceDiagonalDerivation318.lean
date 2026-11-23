module
public import Mathlib.RingTheory.Kaehler.Basic

public section
noncomputable section

namespace SelectedJTraceDiagonalDerivation318

open scoped TensorProduct

variable {A B T : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup T] [Module A T] [Module B T] [IsScalarTower A B T]

/-- A multiplication image of a diagonal annihilator kills relative
derivations. This needs no monogeneity, no residue separability and no
completion. The trace-dual producer of the diagonal annihilator is separate. -/
theorem smul_derivation_eq_zero (D : Derivation A B T) (z : B ⊗[A] B) (a : B)
    (hz : TensorProduct.lmul' (S := B) A z = a)
    (hdiag : ∀ b : B, ((1 : B) ⊗ₜ[A] b - b ⊗ₜ[A] (1 : B)) * z = 0)
    (b : B) :
    a • D b = 0 := by
  have h := congrArg D.tensorProductTo (hdiag b)
  rw [Derivation.tensorProductTo_mul, map_zero] at h
  simpa only [map_sub, TensorProduct.lmul'_apply_tmul, mul_one, one_mul, sub_self, zero_smul,
    zero_add, Derivation.tensorProductTo_tmul, Derivation.map_one_eq_zero, one_smul,
    smul_zero, sub_zero, hz] using h

end SelectedJTraceDiagonalDerivation318

#print axioms SelectedJTraceDiagonalDerivation318.smul_derivation_eq_zero
