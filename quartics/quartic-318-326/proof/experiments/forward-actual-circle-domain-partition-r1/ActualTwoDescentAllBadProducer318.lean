module
public import ActualTwoDescentSameAllBadCards318
public section
noncomputable section
namespace ActualTwoDescentAllBadProducer318
open ActualTwoDescentSameAllBadCards318 ActualTwoDescentAllBadCardinality318
open ActualTwoDescentSimultaneousProducer318 ActualTwoDescentSmallPattern318
open ActualTwoDescentMutualSymbolRows318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentOldCorePreservation318 ActualTwoDescentExtendedVectors318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- Original beta/theta support data PRODUCE arbitrarily large simultaneous
twists with exactly four positive normalized ACTUAL local classes at every
bad prime and infinity. No auxiliary-prime, matrix-kernel, signature or
local-point hypothesis is supplied by the caller. -/
theorem actual_simultaneous_all_bad_classes (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
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
       Nat.card (AllBadSpace p)=4 ∧ Nat.card (AllBadSpace (restricted p))=4) := by
  obtain ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull⟩ :=
    actual_simultaneous_finite_descent d qB qJ hB hJ hdis hβ hθ H forbidden N
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  letI : ∀ i : Index d, Fact (restricted p i).Prime := fun i => ⟨hp (oldEmbedding i)⟩
  exact ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull,
    actual_same_all_bad_cards d p hd qB hBfix hβ N Cfull Csmall⟩

end ActualTwoDescentAllBadProducer318
