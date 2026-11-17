module
public import AuxiliaryLocalUnitClass318
public import LocalNormPrimeSplitting318
public section
namespace AuxiliarySelectedParity318
open scoped BigOperators

/-- The complementary factor of the selected integer is an actual p-unit.
This proves, rather than assumes, the exactly-one-factor premise used by
the checked local norm theorem when the chosen parity exponent is1. -/
theorem selected_factor (S : Finset ℕ) (α : ℕ → ℕ)
    (hS : ∀ p∈S, p.Prime) (σ : ℤ) (hσ : σ=1 ∨ σ= -1)
    (q : ℕ) (hq : q.Prime) (hqS : q∉S) (p : ℕ) (hpS : p∈S) :
    ∃ E : ℤ, ¬(p:ℤ)∣E ∧
      σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ)=(p:ℤ)^α p*E := by
  have hp := hS p hpS
  let R : ℕ := ∏ r∈S.erase p,r^α r
  have hcomp := AuxiliaryLocalUnitClass318.prime_product_complement S α hS p hpS
  have hnot : ¬p∣q := by
    intro hd
    have he : p=q := ((Nat.dvd_prime hq).mp hd).resolve_left hp.ne_one
    exact hqS (he ▸ hpS)
  have hcq : p.Coprime q := hp.coprime_iff_not_dvd.mpr hnot
  have hc : p.Coprime (R*q) := hcomp.2.mul_right hcq
  have hn : ¬p∣R*q := hp.coprime_iff_not_dvd.mp hc
  have hz : ¬(p:ℤ)∣((R*q:ℕ):ℤ) := by exact_mod_cast hn
  let E : ℤ := σ*(R:ℤ)*(q:ℤ)
  have hE : ¬(p:ℤ)∣E := by
    rcases hσ with rfl | rfl <;> simpa [E,Nat.cast_mul] using hz
  refine ⟨E,hE,?_⟩
  rw [hcomp.1]
  dsimp only [E,R]
  push_cast
  ring

/-- Actual A-side local representation of the selected integer forces
splitting2 at each odd selected parity prime. No complementary-unit
assumption or unramified-extension theorem is supplied. -/
theorem jacobi_two_at_selected_factor (S : Finset ℕ) (α : ℕ → ℕ)
    (hS : ∀ p∈S,p.Prime) (σ : ℤ) (hσ : σ=1 ∨ σ= -1)
    (q : ℕ) (hq : q.Prime) (hqS : q∉S)
    (p : ℕ) [Fact p.Prime] (hpS : p∈S) (hp2 : p≠2) (ha : α p=1)
    (X Z : ℚ_[p])
    (hA : X^2-2*Z^2=((σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ):ℤ):ℚ_[p])) :
    jacobiSym 2 p=1 := by
  obtain ⟨E,hE,he⟩ := selected_factor S α hS σ hσ q hq hqS p hpS
  have he' : σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ)=(p:ℤ)*E := by
    simpa only [ha,pow_one] using he
  exact LocalNormPrimeSplitting318.jacobi_two_of_local_odd_factor p hp2 E hE Z X
    (hA.trans (congrArg (fun n : ℤ => (n:ℚ_[p])) he'))

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The selected value is a3-adic unit as a consequence of its actual
A-norm and chosen parity range. This is not a new restriction imposed on
the finite approximation problem. -/
theorem three_unit_of_selected_norm (S : Finset ℕ) (α : ℕ → ℕ)
    (hS : ∀ p∈S,p.Prime) (h3 : 3∈S) (ha : α 3≤1)
    (σ : ℤ) (hσ : σ=1 ∨ σ= -1) (q : ℕ) (hq : q.Prime) (hqS : q∉S)
    (X Z : ℚ_[3])
    (hA : X^2-2*Z^2=((σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ):ℤ):ℚ_[3])) :
    α 3=0 ∧ ¬(3:ℤ)∣σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ) := by
  obtain ⟨E,hE,he⟩ := selected_factor S α hS σ hσ q hq hqS 3 h3
  have ha0 : α 3=0 := by
    by_contra h
    have ha1 : α 3=1 := by omega
    have he' : σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ)=3*E := by
      simpa only [ha1,pow_one,Nat.cast_ofNat] using he
    exact LocalNormPrimeSplitting318.no_three_odd_factor E hE Z X
      (hA.trans (congrArg (fun n : ℤ => (n:ℚ_[3])) he'))
  refine ⟨ha0,?_⟩
  have he' : σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ)=E := by
    simpa only [ha0,pow_zero,one_mul] using he
  rwa [he']

end AuxiliarySelectedParity318
