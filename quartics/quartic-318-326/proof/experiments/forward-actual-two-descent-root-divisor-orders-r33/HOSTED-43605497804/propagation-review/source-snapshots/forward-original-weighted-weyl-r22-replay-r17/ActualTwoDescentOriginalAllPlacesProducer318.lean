module
public import ActualTwoDescentSameAllPlacesBeta318
public section
noncomputable section
namespace ActualTwoDescentOriginalAllPlacesProducer318
set_option maxHeartbeats 16000000

open ActualTwoDescentMordellWeilControl318 ActualTwoDescentOriginalMordellWeilProducer318
open ActualTwoDescentSignedActualCardinality318 ActualTwoDescentSimultaneousProducer318
open ActualTwoDescentSmallPattern318 ActualTwoDescentMutualSymbolRows318
open ActualTwoDescentFiniteConclusion318 ActualTwoDescentOldCorePreservation318
open ActualTwoDescentExtendedVectors318 ActualTwoDescentSameAllPlacesBeta318
open ActualTwoDescentAllPlacesIntersection318 ActualTwoDescentTorsionKummerValues318
open scoped BigOperators

/-- Actual local elliptic representation at every place, with no assertion of global representation. -/
def AllPlacesBeta (n β : ℕ) : Prop := ∃ (hn : n ≠ 0) (hβ : β ≠ 0),
  retainedBetaClass (β : ℚ) (Nat.cast_ne_zero.mpr hβ) ∈
    allPlacesImage (n : ℚ) (Nat.cast_ne_zero.mpr hn)

/-- The original simultaneous producer now supplies genuine all-place beta membership,
actual Mordell-Weil finite generation and rank≤1 for both twists on one support. -/
theorem actual_simultaneous_all_places (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
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
      AllPlacesBeta (∏ i, restricted p i) (∏ b, qB b) := by
  obtain ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull,hcards,Hfull,Hsmall⟩ :=
    actual_simultaneous_mordell_weil d qB qJ hB hJ hdis hβ hθ H forbidden N
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  have hlocal := actual_same_all_places_beta d p hd qB hBfix hβ N Cfull Csmall
  dsimp only at hlocal
  have hb : (∏ b, qB b) ≠ 0 := by intro he; norm_num [he] at hβ
  have hn : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  have hn0 : (∏ i, restricted p i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hp (oldEmbedding i)).ne_zero)
  exact ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull,hcards,Hfull,Hsmall,
    ⟨hn,hb,hlocal.1⟩,⟨hn0,hb,hlocal.2⟩⟩

end ActualTwoDescentOriginalAllPlacesProducer318
