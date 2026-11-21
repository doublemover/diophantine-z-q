module
public import Mathlib
public section
noncomputable section
namespace ActualPointedCyclicPairing318

open scoped BigOperators

/-- Zero-based positive-modulus cyclic translation. Signed steps,
including repeated wraps and modulus one, are admitted. -/
def move {n : ℕ} (hn : 0<n) (s : ℤ) (x : Fin n) : Fin n :=
  ⟨(((x.val:ℤ)+s)%(n:ℤ)).toNat,by
    have hn' : (0:ℤ)<(n:ℤ) := by exact_mod_cast hn
    have h₀ := Int.emod_nonneg ((x.val:ℤ)+s) hn'.ne'
    have h₁ := Int.emod_lt_of_pos ((x.val:ℤ)+s) hn'
    omega⟩

theorem move_val {n : ℕ} (hn : 0<n) (s : ℤ) (x : Fin n) :
    ((move hn s x).val:ℤ)=((x.val:ℤ)+s)%(n:ℤ) := by
  have hn' : (0:ℤ)<(n:ℤ) := by exact_mod_cast hn
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')

theorem move_zero {n : ℕ} (hn : 0<n) (x : Fin n) : move hn 0 x=x := by
  apply Fin.ext
  have hval : (x.val:ℤ)<(n:ℤ) := by exact_mod_cast x.isLt
  have hz : ((move hn 0 x).val:ℤ)=(x.val:ℤ) := by
    rw [move_val,add_zero,Int.emod_eq_of_lt (by positivity) hval]
  exact_mod_cast hz

theorem move_add {n : ℕ} (hn : 0<n) (s t : ℤ) (x : Fin n) :
    move hn t (move hn s x)=move hn (s+t) x := by
  apply Fin.ext
  have h : ((move hn t (move hn s x)).val:ℤ)=((move hn (s+t) x).val:ℤ) := by
    simp only [move_val,Int.emod_add_emod,add_assoc]
  exact_mod_cast h

/-- One bijection for *each* retained transverse parameter. -/
@[expose] def translation {n : ℕ} (hn : 0<n) (s : ℤ) : Fin n ≃ Fin n where
  toFun := move hn s
  invFun := move hn (-s)
  left_inv x := by rw [move_add,add_neg_cancel,move_zero]
  right_inv x := by rw [move_add,neg_add_cancel,move_zero]

theorem translation_apply {n : ℕ} (hn : 0<n) (s : ℤ) (x : Fin n) :
    translation hn s x=move hn s x := rfl

theorem translation_symm_apply {n : ℕ} (hn : 0<n) (s : ℤ) (x : Fin n) :
    (translation hn s).symm x=move hn (-s) x := rfl

/-- Exact single-sequence anchoring: the original two-variable sum
keeps its full counting measure; neither m nor any sign is dropped. -/
theorem anchored_pairing {X M : Type*} [Fintype X] [Fintype M]
    (A : M → X ≃ X) (u : X → ℝ) (C : X × M → ℝ) :
    (∑ z : X × M, u (A z.2 z.1) * C z) =
      ∑ y : X, u y * ∑ m : M, C ((A m).symm y,m) := by
  calc
    _ = ∑ m : M, ∑ x : X, u (A m x) * C (x,m) := by
      rw [Fintype.sum_prod_type,Finset.sum_comm]
    _ = ∑ m : M, ∑ y : X, u y * C ((A m).symm y,m) := by
      apply Finset.sum_congr rfl
      intro m _
      simpa only [Equiv.apply_symm_apply] using
        (Equiv.sum_comp (A m).symm (fun x : X => u (A m x) * C (x,m))).symm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

end ActualPointedCyclicPairing318
