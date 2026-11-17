module
public import ActualTwoDescentSignedComparisons318
public section
noncomputable section
namespace ActualTwoDescentSimultaneousLocalClasses318
open ActualTwoDescentSimultaneousProducer318 ActualTwoDescentSmallPattern318
open ActualTwoDescentMutualSymbolRows318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentOldCorePreservation318 ActualTwoDescentExtendedVectors318
open ActualTwoDescentBaselineSupport318 ActualTwoDescentSignedComparisons318
open ActualTwoDescentComparisonCardinality318
open scoped BigOperators
set_option maxHeartbeats 16000000

lemma actual_conclusion_coprime {U : Type*} [Fintype U] [DecidableEq U]
    (p : Option U → ℕ) (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N) :
    ∀ i, Nat.Coprime (p i) 12 := by
  apply support_coprime_of_unit p
  rw [C.residue]
  exact (ZMod.unitOfCoprime 11 (by decide)).isUnit

/-- Both eight-class comparison spaces are PRODUCED on the same actual
final n and nθ, from original beta/theta support data alone. The result
stops at comparison spaces: no local-image equality or global rational
point realization has been inserted as a hidden assumption. -/
theorem actual_simultaneous_comparison_classes (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
    (qB : BetaIndex d → ℕ) (qJ : J → ℕ) [∀ b, Fact (qB b).Prime] [∀ j, Fact (qJ j).Prime]
    (hB : Function.Injective qB) (hJ : Function.Injective qJ) (hdis : ∀ b j, qB b ≠ qJ j)
    (hβ : ((∏ b, qB b : ℕ) : ZMod 24)=17) (hθ : ((∏ j, qJ j : ℕ) : ZMod 24)=1)
    (H : MutualSymbols qB qJ) (forbidden : Finset ℕ) (N : ℕ) :
    ∃ p : Option (CoreIndex d ⊕ J) → ℕ,
      (∀ i, (p i).Prime) ∧ Function.Injective p ∧
      (∀ b, p (some (Sum.inl (Sum.inl b)))=qB b) ∧
      (∀ j, p (some (Sum.inr j))=qJ j) ∧ p none ∉ forbidden ∧
      (∏ i, p i)=(∏ i, restricted p i)*(∏ j, qJ j) ∧
      Conclusion (restricted p) (selector d) (beta d) N ∧
      Conclusion p (extend (selector d)) (extend (beta d)) N ∧
      Nat.card (ComparisonSpace (restricted p))=4 ∧
      Nat.card (SignedComparisonSpace (restricted p))=8 ∧
      Nat.card (ComparisonSpace p)=4 ∧ Nat.card (SignedComparisonSpace p)=8 := by
  obtain ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull⟩ :=
    actual_simultaneous_finite_descent d qB qJ hB hJ hdis hβ hθ H forbidden N
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  letI : ∀ i : Index d, Fact (restricted p i).Prime := fun i => ⟨hp (oldEmbedding i)⟩
  have hc := actual_conclusion_coprime p _ _ N Cfull
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
  have hs2 : ∀ i : Index d, restricted p i ≠ 2 := fun i => hp2 (oldEmbedding i)
  have hs3 : ∀ i : Index d, restricted p i ≠ 3 := fun i => hp3 (oldEmbedding i)
  refine ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull,?_,?_,?_,?_⟩
  · exact actual_comparison_card (restricted p) hs2 hs3 (selector d) (beta d) N Csmall
      rfl (Sum.inl none) rfl
  · exact actual_signed_comparison_card (restricted p) hs2 hs3 (selector d) (beta d) N Csmall
      rfl (Sum.inl none) rfl
  · exact actual_comparison_card p hp2 hp3 (extend (selector d)) (extend (beta d)) N Cfull
      rfl (Sum.inl (Sum.inl none)) rfl
  · exact actual_signed_comparison_card p hp2 hp3 (extend (selector d)) (extend (beta d)) N Cfull
      rfl (Sum.inl (Sum.inl none)) rfl

end ActualTwoDescentSimultaneousLocalClasses318
