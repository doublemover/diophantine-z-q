module
public import AuxiliarySelectedParity318
public import AuxiliarySplitResidues318
public section
namespace AuxiliarySelectedOddProduct318
open scoped BigOperators

private theorem jacobi_product_one (a : ℤ) (F : Finset ℕ)
    (hn : ∀ p∈F,p≠0) (hj : ∀ p∈F,jacobiSym a p=1) :
    jacobiSym a (∏ p∈F,p)=1 := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert p F hp ih =>
    have hp0 : p≠0 := hn p (Finset.mem_insert_self p F)
    have hnF : ∀ r∈F,r≠0 := fun r hr => hn r (Finset.mem_insert_of_mem hr)
    have hF0 : (∏ r∈F,r)≠0 := Finset.prod_ne_zero_iff.mpr hnF
    rw [Finset.prod_insert hp,jacobiSym.mul_right' a hp0 hF0,
      hj p (Finset.mem_insert_self p F),one_mul]
    exact ih hnF (fun r hr => hj r (Finset.mem_insert_of_mem hr))

private theorem odd_product (F : Finset ℕ) (h : ∀ p∈F,Odd p) : Odd (∏ p∈F,p) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert p F hp ih =>
    rw [Finset.prod_insert hp]
    exact (h p (Finset.mem_insert_self p F)).mul
      (ih (fun r hr => h r (Finset.mem_insert_of_mem hr)))

/-- For the selected odd coefficient-prime collection, actual A norms
produce splitting2; the actual coefficient's modular roots produce
splitting6. Multiplication then derives the aggregate characters and the
residue of P. No aggregate character or residue hypothesis is supplied. -/
theorem selected_product (C : ℤ) (hC : C%24=1)
    (S F : Finset ℕ) (α : ℕ → ℕ) (hS : ∀ p∈S,p.Prime)
    (hFS : F⊆S) (hFC : ∀ p∈F,(p:ℤ)∣C) (hα : ∀ p∈F,α p=1)
    (hsix : ∀ (p : ℕ) [Fact p.Prime], (p:ℤ)∣C → IsSquare (6:ZMod p))
    (σ : ℤ) (hσ : σ=1 ∨ σ= -1) (q : ℕ) (hq : q.Prime) (hqS : q∉S)
    (hA : ∀ p (hp : p∈F), letI : Fact p.Prime := ⟨hS p (hFS hp)⟩;
      ∃ X Z : ℚ_[p], X^2-2*Z^2=
        ((σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ):ℤ):ℚ_[p])) :
    jacobiSym 2 (∏ p∈F,p)=1 ∧ jacobiSym 6 (∏ p∈F,p)=1 ∧
      ((∏ p∈F,p)%24=1 ∨ (∏ p∈F,p)%24=23) := by
  classical
  have hprime : ∀ p∈F,p.Prime := fun p hp => hS p (hFS hp)
  have hp2 : ∀ p∈F,p≠2 := by
    intro p hp he
    have hd := hFC p hp
    subst p
    have hh := Int.dvd_iff_emod_eq_zero.mp hd
    omega
  have hp3 : ∀ p∈F,p≠3 := by
    intro p hp he
    have hd := hFC p hp
    subst p
    have hh := Int.dvd_iff_emod_eq_zero.mp hd
    omega
  have h2 : ∀ p∈F,jacobiSym 2 p=1 := by
    intro p hp
    letI : Fact p.Prime := ⟨hprime p hp⟩
    obtain ⟨X,Z,he⟩ := hA p hp
    exact AuxiliarySelectedParity318.jacobi_two_at_selected_factor
      S α hS σ hσ q hq hqS p (hFS hp) (hp2 p hp) (hα p hp) X Z he
  have h6 : ∀ p∈F,jacobiSym 6 p=1 := by
    intro p hp
    letI : Fact p.Prime := ⟨hprime p hp⟩
    have hnot2 : ¬p∣2 := by
      intro hd
      exact hp2 p hp (((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd).resolve_left (hprime p hp).ne_one)
    have hnot3 : ¬p∣3 := by
      intro hd
      exact hp3 p hp (((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left (hprime p hp).ne_one)
    have hnot : ¬p∣6 := by
      intro hd
      rcases (hprime p hp).dvd_mul.mp (show p∣2*3 by simpa using hd) with h | h
      · exact hnot2 h
      · exact hnot3 h
    have h60 : (6:ZMod p)≠0 := fun h => hnot ((ZMod.natCast_eq_zero_iff 6 p).mp h)
    rw [←jacobiSym.legendreSym.to_jacobiSym p 6]
    exact (legendreSym.eq_one_iff p (by simpa using h60)).mpr (by simpa using hsix p (hFC p hp))
  have hn : ∀ p∈F,p≠0 := fun p hp => (hprime p hp).ne_zero
  have hP2 := jacobi_product_one 2 F hn h2
  have hP6 := jacobi_product_one 6 F hn h6
  have hodd : Odd (∏ p∈F,p) := odd_product F (fun p hp =>
    (hprime p hp).eq_two_or_odd'.resolve_left (hp2 p hp))
  exact ⟨hP2,hP6,AuxiliarySplitResidues318.residue_twentyfour _ hodd hP2 hP6⟩

end AuxiliarySelectedOddProduct318
