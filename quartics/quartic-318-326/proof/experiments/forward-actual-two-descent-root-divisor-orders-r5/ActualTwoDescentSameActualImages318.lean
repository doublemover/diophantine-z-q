module
public import ActualTwoDescentActualImageCardinality318
public section
noncomputable section
namespace ActualTwoDescentSameActualImages318
open ActualTwoDescentActualImageCardinality318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentSmallPattern318 ActualTwoDescentOldCorePreservation318
open ActualTwoDescentExtendedVectors318 ActualTwoDescentSimultaneousLocalClasses318
set_option maxHeartbeats 16000000

/-- Both actual local-image counts occur on the SAME final support. This
consumer uses the already-produced finite conclusions, not new kernel,
core-invertibility, torsion-comparison or local-point assumptions. -/
theorem actual_same_image_cards (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
    (p : Option (CoreIndex d ⊕ J) → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (N : ℕ)
    (C : Conclusion p (extend (selector d)) (extend (beta d)) N)
    (C0 : Conclusion (restricted p) (selector d) (beta d) N) :
    Nat.card (ActualImageSpace p)=4 ∧
    (letI : ∀ i : Index d, Fact (restricted p i).Prime :=
      fun i => inferInstanceAs (Fact (p (oldEmbedding i)).Prime)
     Nat.card (ActualImageSpace (restricted p))=4) := by
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
  exact ⟨actual_image_card_four p hd hp2 hp3 _ _ N C rfl (Sum.inl (Sum.inl none)) rfl,
    actual_image_card_four (restricted p) (hd.comp hemb)
      (fun i => hp2 (oldEmbedding i)) (fun i => hp3 (oldEmbedding i))
      _ _ N C0 rfl (Sum.inl none) rfl⟩

end ActualTwoDescentSameActualImages318
