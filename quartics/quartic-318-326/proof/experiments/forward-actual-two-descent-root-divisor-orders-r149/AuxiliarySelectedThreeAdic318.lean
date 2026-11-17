module
public import AuxiliarySelectedParity318
public import AuxiliaryThreeAdicValue318
public section
namespace AuxiliarySelectedThreeAdic318
open scoped BigOperators
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The selected integer is a3-adic unit by its actual A norm, and has
residue1 by its actual B norm. Thus neither the3-unit condition nor the
residue class is an extra input to auxiliary-prime selection. -/
theorem selected_three_consequence (C : ℤ) (hC : C%3=1)
    (S : Finset ℕ) (α : ℕ → ℕ) (hS : ∀ p∈S,p.Prime) (h3 : 3∈S) (ha : α 3≤1)
    (σ : ℤ) (hσ : σ=1 ∨ σ= -1) (q : ℕ) (hq : q.Prime) (hqS : q∉S)
    (X Z T Y : ℚ_[3])
    (hA : X^2-2*Z^2=((σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ):ℤ):ℚ_[3]))
    (hB : (C:ℚ_[3])*T^2-6*Y^2=((σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ):ℤ):ℚ_[3])) :
    α 3=0 ∧ ¬(3:ℤ)∣σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ) ∧
      (σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ))%3=1 := by
  obtain ⟨ha0,hunit⟩ := AuxiliarySelectedParity318.three_unit_of_selected_norm
    S α hS h3 ha σ hσ q hq hqS X Z hA
  refine ⟨ha0,hunit,?_⟩
  have hCZ := (ZMod.intCast_eq_intCast_iff' C 1 3).mpr (by simpa using hC)
  have htZ := AuxiliaryThreeAdicValue318.selected_unit_mod_three
    C (σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ)) (by simpa using hCZ) hunit T Y hB
  have ht := (ZMod.intCast_eq_intCast_iff'
    (σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ)) 1 3).mp (by simpa using htZ)
  simpa using ht

end AuxiliarySelectedThreeAdic318
