module
public import ActualTwoDescentSameRationalBounds318
public section
noncomputable section
namespace ActualTwoDescentRationalBoundsProducer318
open ActualTwoDescentSameRationalBounds318 ActualTwoDescentSignedActualProducer318
open ActualTwoDescentSignedActualCardinality318
open ActualTwoDescentSimultaneousProducer318 ActualTwoDescentSmallPattern318
open ActualTwoDescentMutualSymbolRows318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentOldCorePreservation318 ActualTwoDescentExtendedVectors318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- Original support data produce simultaneous twists with eight signed actual
local classes and an eight-class bound for EVERY actual rational point.
Existence of a rational point in the beta class is still not asserted. -/
theorem actual_simultaneous_rational_class_bounds (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
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
      RationalEightBound (∏ i, p i) (∏ b, qB b) ∧
      RationalEightBound (∏ i, restricted p i) (∏ b, qB b) := by
  obtain ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull,hcards⟩ :=
    actual_simultaneous_signed_actual_classes d qB qJ hB hJ hdis hβ hθ H forbidden N
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  letI : ∀ i : Index d, Fact (restricted p i).Prime := fun i => ⟨hp (oldEmbedding i)⟩
  exact ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull,hcards,
    actual_same_rational_bounds d p hd qB hBfix N Cfull Csmall⟩

end ActualTwoDescentRationalBoundsProducer318
