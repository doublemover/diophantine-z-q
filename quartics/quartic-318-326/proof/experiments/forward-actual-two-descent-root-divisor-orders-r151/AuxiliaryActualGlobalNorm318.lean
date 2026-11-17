module
public import AuxiliaryGlobalNorm318
public import AuxiliarySelectedParity318
public import AuxiliaryComplementCharacters318
public section
namespace AuxiliaryActualGlobalNorm318
open scoped BigOperators

private theorem square_two_of_character (p : ℕ) [Fact p.Prime]
    (hp2 : p≠2) (hj : jacobiSym 2 p=1) : IsSquare (2:ZMod p) := by
  have hp : p.Prime := Fact.out
  have hn : ¬p∣2 := by
    intro hd
    exact hp2 (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hp.ne_one)
  have hz : (2:ZMod p)≠0 := fun h => hn ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  rw [←jacobiSym.legendreSym.to_jacobiSym p 2] at hj
  have hs := (legendreSym.eq_one_iff p (by simpa using hz)).mp hj
  simpa using hs

/-- The actual selected local A-values and the derived new-prime residue
supply every splitting input of the integral norm constructor. No global
norm, prime-factorization parity or per-prime splitting premise is retained. -/
theorem integer_norm_of_selected_locals (S : Finset ℕ) (α : ℕ → ℕ)
    (hS : ∀ p∈S,p.Prime) (hα : ∀ p∈S,α p≤1)
    (σ : ℤ) (hσ : σ=1 ∨ σ= -1) (q : ℕ) (hq : q.Prime) (hqS : q∉S)
    (hq24 : q%24=1 ∨ q%24=23)
    (hA : ∀ p (hp : p∈S), letI : Fact p.Prime := ⟨hS p hp⟩;
      ∃ X Z : ℚ_[p], X^2-2*Z^2=
        ((σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ):ℤ):ℚ_[p])) :
    ∃ x z : ℤ, x^2-2*z^2=σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ) := by
  have hsplit : ∀ p∈S,Even (α p) ∨ IsSquare (2:ZMod p) := by
    intro p hp
    by_cases ha0 : α p=0
    · exact Or.inl (ha0 ▸ (show Even (0:ℕ) from ⟨0,rfl⟩))
    · have ha1 : α p=1 := by have := hα p hp; omega
      right
      by_cases hp2 : p=2
      · subst p
        exact ⟨0,by decide⟩
      · letI : Fact p.Prime := ⟨hS p hp⟩
        obtain ⟨X,Z,he⟩ := hA p hp
        exact square_two_of_character p hp2
          (AuxiliarySelectedParity318.jacobi_two_at_selected_factor
            S α hS σ hσ q hq hqS p hp hp2 ha1 X Z he)
  letI : Fact q.Prime := ⟨hq⟩
  have hq2 : q≠2 := by rcases hq24 with h | h <;> omega
  have hjq := AuxiliaryComplementCharacters318.two_of_residue q
    (by rcases hq24 with h | h <;> omega)
  exact AuxiliaryGlobalNorm318.integer_selected_norm S α hS hsplit q hq
    (square_two_of_character q hq2 hjq) σ hσ

end AuxiliaryActualGlobalNorm318
