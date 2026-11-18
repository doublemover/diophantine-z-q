module
public import ActualTwoDescentRepresentedThree318
public section
noncomputable section
namespace ActualTwoDescentActualLocalClassBound318
open ActualTwoDescentRepresentedSupport318 ActualTwoDescentRepresentedThree318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentCoordinateSymbols318
open ActualTwoDescentLocalClassification318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentZeroSumCompletion318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Positive normalized representatives lying in the ACTUAL elliptic
Kummer image at every support prime and at3. No matrix or formal torsion
comparison appears in this definition. -/
def BadLocallyRepresented (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (δ : ZMod 2) (u v : Option U → ZMod 2) : Prop :=
  (∀ i, RepresentedAt (p i) (∏ j, p j) (firstRepresentative p δ u) (monomial p v)) ∧
  RepresentedAt 3 (∏ j, p j) (firstRepresentative p δ u) (monomial p v)

/-- Actual local representations supply the three finite equations.
This closes the prior gap from genuine local points to the comparison
space; it does not identify that space with a global Selmer group. -/
theorem actual_local_representation_admissible (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (hn : ((∏ j, p j : ℕ) : ZMod 12)=11)
    (δ : ZMod 2) (u v : Option U → ZMod 2) (H : BadLocallyRepresented p δ u v) :
    Admissible p δ u v := by
  have hn3 : ((∏ j, p j : ℕ) : ZMod 3)=2 := by
    have h := congrArg (ZMod.castHom (by decide : 3 ∣ 12) (ZMod 3)) hn
    simpa using h
  exact ⟨fun i => actual_represented_support p hd hp2 hp3 δ u v i (H.1 i),
    actual_represented_three _ _ _ hn3 (actual_monomial_coprime_three p hp3 v) H.2⟩

/-- Every ACTUAL locally represented positive normalized class is one of
four classes determined by1 and the SAME original beta vector. No actual
rational point or Selmer-rank assertion is inferred from this upper bound. -/
theorem actual_represented_class_bound (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (δ : ZMod 2) (u v : Option U → ZMod 2) (H : BadLocallyRepresented p δ u v) :
    δ=0 ∧ v=0 ∧ ∃ c e : ZMod 2, u=c • ones (Option U)+e • beta :=
  (actual_local_classification p hp2 hp3 a beta N C δ u v).mp
    (actual_local_representation_admissible p hd hp2 hp3 C.residue δ u v H)

end ActualTwoDescentActualLocalClassBound318
