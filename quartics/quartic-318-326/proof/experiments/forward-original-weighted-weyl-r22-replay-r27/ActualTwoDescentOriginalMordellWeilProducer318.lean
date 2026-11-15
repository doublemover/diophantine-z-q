module
public import ActualTwoDescentMordellWeilControl318
public section
noncomputable section
namespace ActualTwoDescentOriginalMordellWeilProducer318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentMordellWeilControl318 ActualTwoDescentOriginalQuotientProducer318
open ActualTwoDescentSignedActualCardinality318 ActualTwoDescentSimultaneousProducer318
open ActualTwoDescentSmallPattern318 ActualTwoDescentMutualSymbolRows318
open ActualTwoDescentFiniteConclusion318 ActualTwoDescentOldCorePreservation318
open ActualTwoDescentExtendedVectors318
open scoped BigOperators

/-- Original support inputs produce ACTUAL Mordell-Weil finite generation,
finite torsion and free rank at most one on BOTH simultaneous twists. -/
theorem actual_simultaneous_mordell_weil (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
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
      MordellWeilControl (∏ i, restricted p i) (∏ b, qB b) := by
  obtain ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull,hcards,Hfull,Hsmall⟩ :=
    actual_simultaneous_quotient_control d qB qJ hB hJ hdis hβ hθ H forbidden N
  have hp0 : ∀ i, p i ≠ 0 := fun i => (hp i).ne_zero
  refine ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull,hcards,?_,?_⟩
  · exact actual_mordell_weil_control _ _
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp0 i)) Hfull
  · exact actual_mordell_weil_control _ _
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp0 (oldEmbedding i))) Hsmall

end ActualTwoDescentOriginalMordellWeilProducer318
