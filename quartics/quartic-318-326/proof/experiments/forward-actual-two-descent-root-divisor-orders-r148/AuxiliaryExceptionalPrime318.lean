module
public import AuxiliaryActualCoefficientCharacters318
public import AuxiliaryComplementCharacters318
public import AuxiliaryPrimeProductAssembly318
public import AuxiliarySelectionCallerBridges318
public section
namespace AuxiliaryExceptionalPrime318

/-- Every prime satisfying the constructed finite local conditions splits
the required coefficient6C. There is no second existential prime choice,
no supplied total Jacobi product, and no assumption of q-adic solubility.
The structural partition and common-value congruences must come from the
actual selected-value construction. -/
theorem square_at_selected_prime (C σ : ℤ) (P U q α : ℕ)
    (hC : C%24=1) (hCs : Squarefree C) (hσ : σ=1 ∨ σ= -1)
    (hfac : C=σ*(P:ℤ)*(U:ℤ)) (hq : q.Prime)
    (hqS : q∉insert 2 (insert 3 C.natAbs.primeFactors))
    (hP24 : P%24=1 ∨ P%24=23) (hα : α=0 ∨ α=1)
    (hdyadic : if α=0 then (σ*(P:ℤ)*(q:ℤ))%8=1
      else (σ*(P:ℤ)*(q:ℤ))%8=7)
    (hthree : (σ*(2:ℤ)^α*(P:ℤ)*(q:ℤ))%3=1)
    (hsix : ∀ (p : ℕ) [Fact p.Prime], (p:ℤ)∣C → IsSquare (6:ZMod p))
    (hA : ∀ (p : ℕ) [Fact p.Prime], (p:ℤ)∣C →
      ∃ X Z : ℚ_[p], X^2-2*Z^2=((σ*2^α*(P:ℤ)*(q:ℤ):ℤ):ℚ_[p]))
    (hB : ∀ (p : ℕ) [Fact p.Prime], (p:ℤ)∣C →
      ∃ T Y : ℚ_[p], (C:ℚ_[p])*T^2-6*Y^2=
        ((σ*2^α*(P:ℤ)*(q:ℤ):ℤ):ℚ_[p])) :
    IsSquare ((6*C:ℤ):ZMod q) := by
  letI : Fact q.Prime := ⟨hq⟩
  have hN : C.natAbs=P*U := by
    have hh := congrArg Int.natAbs hfac
    rcases hσ with rfl | rfl <;> simpa [Int.natAbs_mul] using hh
  have hsN : Squarefree (P*U) := by
    rw [←hN]
    exact Int.squarefree_natAbs.mpr hCs
  have hcop : P.Coprime U := Nat.coprime_of_squarefree_mul hsN
  have hcopZ : (U:ℤ).gcd P=1 := by
    simpa only [Int.gcd_natCast_natCast] using hcop.symm.gcd_eq_one
  have hP : Odd P := Nat.odd_iff.mpr (by rcases hP24 with h | h <;> omega)
  have hUno : ¬2∣U := by
    intro hd
    have hn : 2∣C.natAbs := by rw [hN]; exact dvd_mul_of_dvd_right hd P
    have hz : (2:ℤ)∣C := Int.natAbs_dvd_natAbs.mp (by simpa using hn)
    have hm := Int.dvd_iff_emod_eq_zero.mp hz
    omega
  have hU : Odd U := by
    apply Nat.odd_iff.mpr
    have hz : U%2≠0 := fun h => hUno (Nat.dvd_of_mod_eq_zero h)
    omega
  have h2P : jacobiSym 2 P=1 := AuxiliaryComplementCharacters318.two_of_residue P
    (by rcases hP24 with h | h <;> omega)
  have h2U := AuxiliaryComplementCharacters318.two_complement C P U hC hN h2P
  have hq24 := AuxiliaryComplementCharacters318.prime_residue_of_common_value
    σ P q α hσ hP24 hα hdyadic hthree
  have hqodd : Odd q := Nat.odd_iff.mpr (by rcases hq24 with h | h <;> omega)
  have h6q := AuxiliaryComplementCharacters318.six_of_twentyfour q hq24
  have he : C=σ*((P*U:ℕ):ℤ) := by simpa only [Nat.cast_mul,mul_assoc] using hfac
  have hsign := AuxiliarySelectionCallerBridges318.character_sign_compatibility
    C hC (P*U) σ hσ he
  obtain ⟨hselected,hunselected⟩ := AuxiliaryActualCoefficientCharacters318.identities
    C σ σ P U q α hC hCs hσ hσ hfac hq hqS hsix hA hB
  exact AuxiliaryPrimeProductAssembly318.square_six_coefficient
    C P U q α hC hN hqodd hP hU hcopZ σ σ hσ hsign h2U h6q
      hselected hunselected

end AuxiliaryExceptionalPrime318
