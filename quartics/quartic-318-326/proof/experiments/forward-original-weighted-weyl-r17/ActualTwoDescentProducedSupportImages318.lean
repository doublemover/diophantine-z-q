module
public import ActualTwoDescentOddSupportImage318
public section
noncomputable section
namespace ActualTwoDescentProducedSupportImages318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentZeroSumCompletion318
open ActualTwoDescentGoodPrimeValuations318 ActualTwoDescentOddSupportImage318
open ActualTwoDescentTorsionSquarePairs318 ActualTwoDescentOldCorePreservation318
open ActualTwoDescentFiniteConclusion318 ActualTwoDescentSimultaneousLocalClasses318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- The actual squarefree product has valuation1 at every indexed prime;
this is obtained from the literal prime monomial, not a local hypothesis. -/
lemma actual_product_support_valuation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p) (i : ι) :
    (((∏ j, p j : ℕ) : ℚ_[p i])).valuation=1 := by
  have h := actual_monomial_valuation p hd (ones ι) i
  have hn : monomial p (ones ι)=∏ j, p j := by simp [monomial,ones]
  rw [Padic.valuation_natCast]
  simpa only [hn,ones,ZMod.val_one,Int.natCast_one] using congrArg (fun n : ℕ => (n : ℤ)) h

/-- Uniform actual local-image containment at every support prime of the
constructed squarefree product. All four torsion possibilities retain
explicit nonzero square multipliers in the correct completed field. -/
theorem actual_prime_support_images {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hc : ∀ i, Nat.Coprime (p i) 12) :
    ∀ i, ∀ P : LocalPoint (p:=p i) (∏ j, p j),
      TorsionPair (((∏ j, p j : ℕ) : ℚ_[p i]))
        (P.x+3*(∏ j, p j : ℕ)) (P.x-(∏ j, p j : ℕ)) := by
  intro i P
  have hp2 : p i ≠ 2 := by
    intro he
    have h := hc i
    rw [he] at h
    norm_num at h
  have hp3 : p i ≠ 3 := by
    intro he
    have h := hc i
    rw [he] at h
    norm_num at h
  exact actual_odd_support_image _ hp2 hp3 (actual_product_support_valuation p hd i) P

/-- Both same-support finite conclusions now consume genuine elliptic
local-image containment, not an assumed torsion-comparison condition. -/
theorem actual_same_support_odd_images {U J : Type*} [Fintype U] [DecidableEq U]
    [Fintype J] [DecidableEq J] (p : Option (U ⊕ J) → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (a beta : Option (U ⊕ J) → ZMod 2)
    (a0 beta0 : Option U → ZMod 2) (N : ℕ)
    (C : Conclusion p a beta N) (C0 : Conclusion (restricted p) a0 beta0 N) :
    (∀ i, ∀ P : LocalPoint (p:=p i) (∏ j, p j),
      TorsionPair (((∏ j, p j : ℕ) : ℚ_[p i]))
        (P.x+3*(∏ j, p j : ℕ)) (P.x-(∏ j, p j : ℕ))) ∧
    (∀ i : Option U, ∀ P : LocalPoint (p:=p (oldEmbedding i)) (∏ j, restricted p j),
      TorsionPair (((∏ j, restricted p j : ℕ) : ℚ_[p (oldEmbedding i)]))
        (P.x+3*(∏ j, restricted p j : ℕ)) (P.x-(∏ j, restricted p j : ℕ))) := by
  letI : ∀ i : Option U, Fact (restricted p i).Prime := fun i => inferInstanceAs (Fact (p (oldEmbedding i)).Prime)
  have hemb : Function.Injective (oldEmbedding : Option U → Option (U ⊕ J)) := by
    intro i j he
    cases i <;> cases j <;> simp_all [oldEmbedding]
  exact ⟨actual_prime_support_images p hd (actual_conclusion_coprime p a beta N C),
    actual_prime_support_images (restricted p) (hd.comp hemb)
      (actual_conclusion_coprime (restricted p) a0 beta0 N C0)⟩

end ActualTwoDescentProducedSupportImages318
