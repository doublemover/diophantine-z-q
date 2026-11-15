module
public import ActualTwoDescentSameAllPlacesCardinality318
public section
noncomputable section
namespace ActualTwoDescentOriginalAllPlacesCardinality318
set_option maxHeartbeats 16000000

open ActualTwoDescentOriginalAllPlacesProducer318 ActualTwoDescentMordellWeilControl318
open ActualTwoDescentSameAllPlacesCardinality318 ActualTwoDescentAllPlacesIntersection318
open ActualTwoDescentSignedActualCardinality318 ActualTwoDescentSimultaneousProducer318
open ActualTwoDescentSmallPattern318 ActualTwoDescentMutualSymbolRows318
open ActualTwoDescentFiniteConclusion318 ActualTwoDescentOldCorePreservation318
open ActualTwoDescentExtendedVectors318
open scoped BigOperators

def AllPlacesEight (n : ℕ) : Prop := ∃ hn : n ≠ 0,
  Nat.card (allPlacesImage (n : ℚ) (Nat.cast_ne_zero.mpr hn))=8

/-- Original prime inputs produce exact cardinality EIGHT for the actual all-place
intersection on both twists. The actual rational image may still have cardinality four. -/
theorem actual_simultaneous_all_places_eight (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
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
      MordellWeilControl (∏ i, p i) (∏ b, qB b) ∧
      MordellWeilControl (∏ i, restricted p i) (∏ b, qB b) ∧
      AllPlacesBeta (∏ i, p i) (∏ b, qB b) ∧
      AllPlacesBeta (∏ i, restricted p i) (∏ b, qB b) ∧
      AllPlacesEight (∏ i, p i) ∧ AllPlacesEight (∏ i, restricted p i) := by
  obtain ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull,hcards,Hfull,Hsmall,Lfull,Lsmall⟩ :=
    actual_simultaneous_all_places d qB qJ hB hJ hdis hβ hθ H forbidden N
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  have hn : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  have hn0 : (∏ i, restricted p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hp (oldEmbedding i)).ne_zero)
  have hactual := actual_same_all_places_cardinality d p hd qB hBfix hβ N Cfull Csmall hn hn0
  exact ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull,hcards,Hfull,Hsmall,Lfull,Lsmall,
    ⟨hn,hactual.1⟩,⟨hn0,hactual.2⟩⟩

end ActualTwoDescentOriginalAllPlacesCardinality318
