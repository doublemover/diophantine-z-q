module
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public section

namespace FiniteModuleRationalization318
open scoped TensorProduct

/-- A finite module vanishes after base change to a characteristic-zero
field. The proof kills each pure tensor using its actual additive order. -/
theorem subsingleton_tensor_of_finite (R K M : Type*) [CommRing R] [Field K]
    [CharZero K] [Algebra R K] [AddCommGroup M] [Module R M] [Finite M] :
    Subsingleton (K ⊗[R] M) := by
  have hz (x : K ⊗[R] M) : x = 0 := by
    refine TensorProduct.inductionOn x ?_ ?_
    · intro q m
      obtain ⟨k,hk,hkm⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (isOfFinAddOrder_of_finite m)
      let q' : K := (k:K)⁻¹ * q
      have hq : (k:R) • q' = q := by
        calc
          (k:R) • q' = k • q' := Nat.cast_smul_eq_nsmul R _ _
          _ = (k:K) • q' := (Nat.cast_smul_eq_nsmul K _ _).symm
          _ = q := by
            rw [smul_eq_mul]
            dsimp only [q']
            rw [←mul_assoc,mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk.ne'),one_mul]
      have hm : (k:R) • m = 0 := by rw [Nat.cast_smul_eq_nsmul,hkm]
      calc
        q ⊗ₜ[R] m = ((k:R) • q') ⊗ₜ[R] m := by rw [hq]
        _ = q' ⊗ₜ[R] ((k:R) • m) := TensorProduct.smul_tmul _ _ _
        _ = 0 := by rw [hm,TensorProduct.tmul_zero]
    · intro x y hx hy
      rw [hx,hy,add_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end FiniteModuleRationalization318

#print axioms FiniteModuleRationalization318.subsingleton_tensor_of_finite
