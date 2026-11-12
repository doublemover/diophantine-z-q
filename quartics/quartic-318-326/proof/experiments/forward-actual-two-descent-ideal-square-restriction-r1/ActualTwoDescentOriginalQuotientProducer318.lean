module
public import ActualTwoDescentSameActualQuotientControl318
public section
noncomputable section
namespace ActualTwoDescentOriginalQuotientProducer318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentActualQuotientControl318 ActualTwoDescentSameActualQuotientControl318
open ActualTwoDescentRationalBoundsProducer318 ActualTwoDescentSignedActualCardinality318
open ActualTwoDescentSimultaneousProducer318 ActualTwoDescentSmallPattern318
open ActualTwoDescentMutualSymbolRows318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentOldCorePreservation318 ActualTwoDescentExtendedVectors318
open scoped BigOperators

/-- Original support inputs now produce finite actual E(Q)/2E(Q) on both
twists, with at most eight elements and the exact cardinality-to-point consumer. -/
theorem actual_simultaneous_quotient_control (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
    (qB : BetaIndex d → ℕ) (qJ : J → ℕ) [∀ b, Fact (qB b).Prime] [∀ j, Fact (qJ j).Prime]
    (hB : Function.Injective qB) (hJ : Function.Injective qJ) (hdis : ∀ b j, qB b ≠ qJ j)
    (hβ : ((∏ b, qB b : ℕ) : ZMod 24)=17) (hθ : ((∏ j, qJ j : ℕ) : ZMod 24)=1)
    (H : MutualSymbols qB qJ) (forbidden : Finset ℕ) (N : ℕ) :
    ∃ (p : Option (CoreIndex d ⊕ J) → ℕ) (hp : ∀ i, (p i).Prime),
      Function.Injective p ∧
      (∀ b, p (some (Sum.inl (Sum.inl b)))=qB b) ∧
      (∀ j, p (some (Sum.inr j))=qJ j) ∧ p none ∉ forbidden ∧
      (∏ i, p i)=(∏ i, restricted p i)*(∏ j, qJ j) ∧
      Conclusion (restricted p) (selector d) (beta d) N ∧
      Conclusion p (extend (selector d)) (extend (beta d)) N ∧
      (letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
       letI : ∀ i : Index d, Fact (restricted p i).Prime := fun i => ⟨hp (oldEmbedding i)⟩
       Nat.card (SignedActualSpace p)=8 ∧ Nat.card (SignedActualSpace (restricted p))=8) ∧
      QuotientControl (∏ i, p i) (∏ b, qB b) ∧
      QuotientControl (∏ i, restricted p i) (∏ b, qB b) := by
  obtain ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull,hcards,Hfull,Hsmall⟩ :=
    actual_simultaneous_rational_class_bounds d qB qJ hB hJ hdis hβ hθ H forbidden N
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  exact ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull,hcards,
    actual_same_quotient_control d p hd qB hBfix N Cfull Csmall⟩

end ActualTwoDescentOriginalQuotientProducer318
