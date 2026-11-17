module
public import AuxiliarySupportFactorization318
public import AuxiliarySelectedThreeAdic318
public import AuxiliarySelectedOddProduct318
public import AuxiliarySelectedDyadicBound318
public import AuxiliaryExceptionalPrime318
public section
noncomputable section
namespace AuxiliarySelectedCompatibility318
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Instantiate the structural partition, parity and local character
lemmas on one actual selected value over the fixed coefficient support.
No P/U factorization, residue, character product or new-prime square is
assumed. All are derived from the supplied actual common finite values. -/
theorem compatible (C σ : ℤ) (α : ℕ → ℕ) (q : ℕ)
    (hC : C%24=1) (hCs : Squarefree C) (hσ : σ=1 ∨ σ= -1)
    (hCσ : C=σ*(C.natAbs:ℤ)) (hα : ∀ p,α p≤1)
    (hq : q.Prime) (hqS : q∉insert 2 (insert 3 C.natAbs.primeFactors))
    (hsix : ∀ (p : ℕ) [Fact p.Prime], (p:ℤ)∣C → IsSquare (6:ZMod p))
    (hlocal : ∀ p (hp : p∈insert 2 (insert 3 C.natAbs.primeFactors)),
      ∀ [Fact p.Prime], ∃ X Z T Y : ℚ_[p],
        X^2-2*Z^2=((σ*((∏ r∈insert 2 (insert 3 C.natAbs.primeFactors),r^α r):ℕ)*(q:ℤ):ℤ):ℚ_[p]) ∧
        (C:ℚ_[p])*T^2-6*Y^2=((σ*((∏ r∈insert 2 (insert 3 C.natAbs.primeFactors),r^α r):ℕ)*(q:ℤ):ℤ):ℚ_[p])) :
    (q%24=1 ∨ q%24=23) ∧ IsSquare ((6*C:ℤ):ZMod q) := by
  classical
  let J := C.natAbs.primeFactors
  let S := insert 2 (insert 3 J)
  let F := J.filter (fun p => α p=1)
  let P := ∏ p∈F,p
  let U := ∏ p∈J.filter (fun p => α p≠1),p
  let D := ∏ p∈S,p^α p
  let t : ℤ := σ*(D:ℤ)*(q:ℤ)
  have hC0 : C≠0 := by intro hz; subst C; norm_num at hC
  have hS : ∀ p∈S,p.Prime := by
    intro p hp
    simp only [S,Finset.mem_insert] at hp
    rcases hp with rfl | rfl | hp
    · exact Nat.prime_two
    · decide
    · exact (Nat.mem_primeFactors.mp hp).1
  have h2S : 2∈S := Finset.mem_insert_self _ _
  have h3S : 3∈S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  obtain ⟨X3,Z3,T3,Y3,hA3,hB3⟩ := hlocal 3 h3S
  obtain ⟨ha3,_,ht3⟩ := AuxiliarySelectedThreeAdic318.selected_three_consequence
    C (by omega) S α hS h3S (hα 3) σ hσ q hq hqS X3 Z3 T3 Y3 hA3 hB3
  have hfac := AuxiliarySupportFactorization318.actual_coefficient_factorization
    C hC hCs α (fun p _ => hα p) ha3
  change C.natAbs=P*U ∧ P.Coprime U ∧ D=2^α 2*P at hfac
  obtain ⟨hN,_,hD⟩ := hfac
  have hFS : F⊆S := by
    intro p hp
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.mp hp).1)
  have hFC : ∀ p∈F,(p:ℤ)∣C := by
    intro p hp
    have hd := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).2.1
    exact Int.natAbs_dvd_natAbs.mp (by simpa using hd)
  have hFα : ∀ p∈F,α p=1 := fun p hp => (Finset.mem_filter.mp hp).2
  have hAF : ∀ p (hp : p∈F), letI : Fact p.Prime := ⟨hS p (hFS hp)⟩;
      ∃ X Z : ℚ_[p], X^2-2*Z^2=(t:ℚ_[p]) := by
    intro p hp
    letI : Fact p.Prime := ⟨hS p (hFS hp)⟩
    obtain ⟨X,Z,T,Y,hA,_⟩ := hlocal p (hFS hp)
    exact ⟨X,Z,hA⟩
  obtain ⟨_,_,hP24⟩ := AuxiliarySelectedOddProduct318.selected_product
    C hC S F α hS hFS hFC hFα hsix σ hσ q hq hqS hAF
  obtain ⟨X2,Z2,T2,Y2,hA2,hB2⟩ := hlocal 2 h2S
  obtain ⟨_,_,hodd,heven⟩ := AuxiliarySelectedDyadicBound318.selected_bound_and_half_residue
    C (by omega) S α hS h2S (hα 2) σ hσ q hq hqS X2 Z2 T2 Y2 hA2 hB2
  have ht : t=σ*(2:ℤ)^α 2*(P:ℤ)*(q:ℤ) := by
    dsimp only [t]
    rw [hD]
    push_cast
    ring
  have ha2 : α 2=0 ∨ α 2=1 := by have := hα 2; omega
  have hdyadic : if α 2=0 then (σ*(P:ℤ)*(q:ℤ))%8=1
      else (σ*(P:ℤ)*(q:ℤ))%8=7 := by
    rcases ha2 with h0 | h1
    · have hh := (hodd h0).2
      change t%8=1 at hh
      simpa only [ht,h0,pow_zero,mul_one,if_pos rfl] using hh
    · have hh := (heven h1).2
      change (t/2)%8=7 at hh
      have ht' : t=2*(σ*(P:ℤ)*(q:ℤ)) := by rw [ht,h1]; ring
      have hdiv : t/2=σ*(P:ℤ)*(q:ℤ) := by rw [ht']; omega
      simpa only [h1,show (1:ℕ)≠0 by decide,if_false,hdiv] using hh
  have hthree : (σ*(2:ℤ)^α 2*(P:ℤ)*(q:ℤ))%3=1 := by
    change t%3=1 at ht3
    rwa [ht] at ht3
  have hq24 := AuxiliaryComplementCharacters318.prime_residue_of_common_value
    σ P q (α 2) hσ hP24 ha2 hdyadic hthree
  refine ⟨hq24,?_⟩
  have hCfac : C=σ*(P:ℤ)*(U:ℤ) := by
    rw [hCσ,hN]
    push_cast
    ring
  apply AuxiliaryExceptionalPrime318.square_at_selected_prime
    C σ P U q (α 2) hC hCs hσ hCfac hq hqS hP24 ha2 hdyadic hthree hsix
  · intro p inst hpC
    have hp : p.Prime := Fact.out
    have hpS := AuxiliarySelectionCallerBridges318.coefficient_prime_mem C hC0 p hp hpC
    obtain ⟨X,Z,T,Y,hA,_⟩ := hlocal p hpS
    refine ⟨X,Z,?_⟩
    change X^2-2*Z^2=(t:ℚ_[p]) at hA
    simpa only [ht] using hA
  · intro p inst hpC
    have hp : p.Prime := Fact.out
    have hpS := AuxiliarySelectionCallerBridges318.coefficient_prime_mem C hC0 p hp hpC
    obtain ⟨X,Z,T,Y,_,hB⟩ := hlocal p hpS
    refine ⟨T,Y,?_⟩
    change (C:ℚ_[p])*T^2-6*Y^2=(t:ℚ_[p]) at hB
    simpa only [ht] using hB

end AuxiliarySelectedCompatibility318
