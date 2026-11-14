module
public import ActualTwoDescentOriginalBetaResidue318
public section
noncomputable section
namespace ActualTwoDescentSameAllBadCards318
open ActualTwoDescentOriginalBetaResidue318 ActualTwoDescentAllBadCardinality318
open ActualTwoDescentFiniteConclusion318 ActualTwoDescentSimultaneousLocalClasses318
open ActualTwoDescentSmallPattern318 ActualTwoDescentOldCorePreservation318
open ActualTwoDescentExtendedVectors318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- Both exact counts include2,3,EVERY support prime and infinity, using
the SAME final support and original beta product. -/
theorem actual_same_all_bad_cards (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
    (p : Option (CoreIndex d ⊕ J) → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (qB : BetaIndex d → ℕ)
    (hB : ∀ b, p (some (Sum.inl (Sum.inl b)))=qB b)
    (hβ : ((∏ b, qB b : ℕ) : ZMod 24)=17) (N : ℕ)
    (C : Conclusion p (extend (selector d)) (extend (beta d)) N)
    (C0 : Conclusion (restricted p) (selector d) (beta d) N) :
    Nat.card (AllBadSpace p)=4 ∧
    (letI : ∀ i : Index d, Fact (restricted p i).Prime :=
      fun i => inferInstanceAs (Fact (p (oldEmbedding i)).Prime)
     Nat.card (AllBadSpace (restricted p))=4) := by
  letI : ∀ i : Index d, Fact (restricted p i).Prime :=
    fun i => inferInstanceAs (Fact (p (oldEmbedding i)).Prime)
  have hemb : Function.Injective (oldEmbedding : Index d → Option (CoreIndex d ⊕ J)) := by
    intro i j he
    cases i <;> cases j <;> simp_all [oldEmbedding]
  have hc := actual_conclusion_coprime p _ _ N C
  have hp2 : ∀ i, p i ≠ 2 := by
    intro i he
    have h := hc i
    rw [he] at h
    norm_num at h
  have hp3 : ∀ i, p i ≠ 3 := by
    intro i he
    have h := hc i
    rw [he] at h
    norm_num at h
  obtain ⟨hb,hb0⟩ := actual_original_beta_residues d p qB hB hβ
  exact ⟨actual_all_bad_card_four p hd hp2 hp3 _ _ N C hb rfl (Sum.inl (Sum.inl none)) rfl,
    actual_all_bad_card_four (restricted p) (hd.comp hemb)
      (fun i => hp2 (oldEmbedding i)) (fun i => hp3 (oldEmbedding i))
      _ _ N C0 hb0 rfl (Sum.inl none) rfl⟩

end ActualTwoDescentSameAllBadCards318
