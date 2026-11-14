module
public import ActualTwoDescentExceptionalLocalPoints318
public section
noncomputable section
namespace ActualTwoDescentBetaSupportSquares318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentStrippedSymbols318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentTorsionComparison318
open ActualTwoDescentSignReciprocity318 ActualTwoDescentZeroSumCompletion318
open ActualTwoDescentJacobiPadicSquare318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma actual_stripped_pos (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (b : ι → ZMod 2) (i : ι) : 0 < stripped p b i := by
  apply Finset.prod_pos
  intro j _
  exact pow_pos (Fact.out : (p j).Prime).pos _

/-- The ACTUAL kernel equation gives actual Q_q square witnesses for beta
or beta/n at every support prime. In the valuation1 case the prime is
removed from BOTH literal integer products before Hensel is applied. -/
theorem actual_beta_support_squarecases (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2)
    (b : ι → ZMod 2) (hK : laplacian p *ᵥ b=0) (i : ι) :
    (∃ r : ℚ_[p i], r ≠ 0 ∧ (monomial p b : ℚ_[p i])=r^2) ∨
    (∃ r : ℚ_[p i], r ≠ 0 ∧ (monomial p b : ℚ_[p i])=
      ((∏ j, p j : ℕ) : ℚ_[p i])*r^2) := by
  have hrow : (edges p *ᵥ b) i+row p i*b i=0 := by
    simpa only [actual_row_action,Pi.zero_apply] using congrFun hK i
  have hfactor := actual_stripped_factor p b i
  by_cases hbi : b i=0
  · simp only [hbi,ZMod.val_zero,pow_zero,one_mul] at hfactor
    have hEu : (edges p *ᵥ b) i=0 := by simpa only [hbi,mul_zero,add_zero] using hrow
    have hJ : jacobiSym (monomial p b : ℤ) (p i)=1 := by
      rw [hfactor,actual_stripped_symbol p hd,hEu,sign_zero]
    have hcop : Nat.Coprime (monomial p b) (p i) := by
      rw [hfactor]
      exact actual_stripped_coprime p hd b i
    obtain ⟨r,hr,he⟩ := actual_jacobi_padic_unit_square (hp2 i) _ (monomial_pos p b).ne' hcop hJ
    exact Or.inl ⟨r,hr,he.symm⟩
  · have hbi1 : b i=1 := by fin_cases b i <;> norm_num at hbi ⊢
    simp only [hbi1,ZMod.val_one,pow_one] at hfactor
    have hrow' : (edges p *ᵥ b) i+row p i=0 := by simpa only [hbi1,mul_one] using hrow
    have hmon : monomial p (ones ι)=∏ j, p j := by simp [monomial,ones]
    have hnfac : (∏ j, p j)=p i*stripped p (ones ι) i := by
      simpa only [hmon,ones,ZMod.val_one,pow_one] using actual_stripped_factor p (ones ι) i
    have hones : (edges p *ᵥ ones ι) i=row p i := by
      simp only [Matrix.mulVec,dotProduct,ones,mul_one,row]
    have hJ : jacobiSym ((stripped p b i*stripped p (ones ι) i : ℕ) : ℤ) (p i)=1 := by
      rw [Nat.cast_mul,jacobiSym.mul_left,actual_stripped_symbol p hd,
        actual_stripped_symbol p hd,←sign_add,hones,hrow',sign_zero]
    have hcop : Nat.Coprime (stripped p b i*stripped p (ones ι) i) (p i) :=
      (actual_stripped_coprime p hd b i).mul_left (actual_stripped_coprime p hd (ones ι) i)
    obtain ⟨r,hr,he⟩ := actual_jacobi_padic_unit_square (hp2 i) _
      (mul_ne_zero (actual_stripped_pos p b i).ne' (actual_stripped_pos p (ones ι) i).ne') hcop hJ
    have hv : (stripped p (ones ι) i : ℚ_[p i]) ≠ 0 :=
      Nat.cast_ne_zero.mpr (actual_stripped_pos p (ones ι) i).ne'
    refine Or.inr ⟨r/stripped p (ones ι) i,div_ne_zero hr hv,?_⟩
    rw [hfactor,hnfac,Nat.cast_mul,Nat.cast_mul,div_pow,he,Nat.cast_mul]
    field_simp [hv]
    <;> ring

end ActualTwoDescentBetaSupportSquares318
