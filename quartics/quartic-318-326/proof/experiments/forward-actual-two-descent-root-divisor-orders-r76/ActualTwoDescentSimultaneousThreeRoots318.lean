module
public import ActualTwoDescentMutualPadicRoots318
public section
noncomputable section
namespace ActualTwoDescentSimultaneousThreeRoots318
open ActualTwoDescentSimultaneousProducer318 ActualTwoDescentSmallPattern318
open ActualTwoDescentMutualSymbolRows318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentOldCorePreservation318 ActualTwoDescentExtendedVectors318
open ActualTwoDescentThreeAdicTorsion318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- The actual first-torsion comparison at3 is produced for BOTH twists
at the SAME final support, with literal nonzero Q_3 square roots. -/
theorem actual_simultaneous_three_roots (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
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
      (∃ r : ℚ_[3], r ≠ 0 ∧ ((∏ b, qB b : ℕ) : ℚ_[3])=
        ((∏ i, restricted p i : ℕ) : ℚ_[3])*r^2) ∧
      (∃ r : ℚ_[3], r ≠ 0 ∧ ((∏ b, qB b : ℕ) : ℚ_[3])=
        ((∏ i, p i : ℕ) : ℚ_[3])*r^2) := by
  obtain ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull⟩ :=
    actual_simultaneous_finite_descent d qB qJ hB hJ hdis hβ hθ H forbidden N
  refine ⟨p,hp,hd,hBfix,hJfix,havoid,hfactor,Csmall,Cfull,?_,?_⟩
  · exact actual_beta_three_torsion _ _ (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le N) Csmall.large))
      hβ Csmall.residue
  · exact actual_beta_three_torsion _ _ (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le N) Cfull.large))
      hβ Cfull.residue

end ActualTwoDescentSimultaneousThreeRoots318
