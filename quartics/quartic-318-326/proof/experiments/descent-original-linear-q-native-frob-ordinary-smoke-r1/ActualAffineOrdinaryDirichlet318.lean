module
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Tactic
public section
noncomputable section
namespace ActualAffineOrdinaryDirichlet318
open scoped BigOperators
open Classical
open ArithmeticFunction

@[expose] def unitCells (F : ℕ) [NeZero F] : Finset (ZMod F) :=
  Finset.univ.filter IsUnit

/-- The ordinary comparison weight uses the true von Mangoldt
function and a fixed cyclic abelian conditional mean. The identity
does not replace this by the constant one on arbitrary progressions. -/
theorem periodic_model_cells {F : ℕ} [NeZero F]
    (α : ZMod F → ℂ) (hα : ∀ a, ¬ IsUnit a → α a=0) (n : ℕ) :
    α (n:ZMod F)*(vonMangoldt n:ℂ) =
      ∑ a ∈ unitCells F, α a*(vonMangoldt.residueClass a n:ℂ) := by
  classical
  by_cases h : IsUnit (n:ZMod F)
  · have hm : (n:ZMod F) ∈ unitCells F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
    symm
    calc
      _ = α (n:ZMod F)*(vonMangoldt.residueClass (n:ZMod F) n:ℂ) := by
        apply Finset.sum_eq_single_of_mem _ hm
        intro a ha hne
        have he : (n:ZMod F) ≠ a := Ne.symm hne
        simp [ArithmeticFunction.vonMangoldt.residueClass,he]
      _ = _ := by simp [ArithmeticFunction.vonMangoldt.residueClass]
  · rw [hα _ h,zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    have hu := (Finset.mem_filter.mp ha).2
    have he : (n:ZMod F) ≠ a := fun e => h (e.symm ▸ hu)
    simp [ArithmeticFunction.vonMangoldt.residueClass,he]

/-- Actual pinned Dirichlet-character expansion of the ordinary model,
with the abelian fibre multiplier α still on the same residue. This
finite Fourier algebra is not Chebotarev affine correlations. -/
theorem periodic_model_characters {F : ℕ} [NeZero F]
    (α : ZMod F → ℂ) (hα : ∀ a, ¬ IsUnit a → α a=0) (n : ℕ) :
    α (n:ZMod F)*(vonMangoldt n:ℂ) =
      ∑ a ∈ unitCells F, α a*((F.totient:ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ F, χ a⁻¹ * χ (n:ZMod F) * (vonMangoldt n:ℂ)) := by
  rw [periodic_model_cells α hα n]
  apply Finset.sum_congr rfl
  intro a ha
  have hu : IsUnit a := (Finset.mem_filter.mp ha).2
  rw [ArithmeticFunction.vonMangoldt.residueClass_apply hu n]

end ActualAffineOrdinaryDirichlet318
