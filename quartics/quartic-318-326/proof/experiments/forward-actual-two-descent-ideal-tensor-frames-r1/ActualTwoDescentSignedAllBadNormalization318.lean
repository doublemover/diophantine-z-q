module
public import ActualTwoDescentSignedRealNormalization318
public section
noncomputable section
namespace ActualTwoDescentSignedAllBadNormalization318
open ActualTwoDescentSignedLocalTranslation318 ActualTwoDescentSignedLocalNormalization318
open ActualTwoDescentSignedRealNormalization318 ActualTwoDescentAllBadEquivalence318
open ActualTwoDescentActualLocalClassBound318 ActualTwoDescentSignedComparisons318
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- ACTUAL signed local curve-image conditions at2,3,each support prime
and the real place, without referring to any formal comparison space. -/
def SignedAllBadRepresented (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (ε δ : ZMod 2) (u v : Option U → ZMod 2) : Prop :=
  (∀ i, SignedRepresentedAt (p i) p ε δ u v) ∧
  SignedRepresentedAt 3 p ε δ u v ∧ SignedRepresentedAt 2 p ε δ u v ∧
  SignedRealRepresented p ε δ u v

/-- Uniform actual torsion normalization identifies the complete signed
bad-place conditions with the positive normalized actual conditions. -/
theorem actual_signed_all_bad_normalization (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (ε δ : ZMod 2) (u v : Option U → ZMod 2) :
    SignedAllBadRepresented p ε δ u v ↔ AllBadRepresented p (δ+ε) u (toggle ε v) := by
  constructor
  · rintro ⟨hS,h3,h2,hR⟩
    exact ⟨⟨fun i => (actual_signed_local_normalization (p i) p ε δ u v).mp (hS i),
      (actual_signed_local_normalization 3 p ε δ u v).mp h3⟩,
      (actual_signed_local_normalization 2 p ε δ u v).mp h2,
      (actual_signed_real_normalization p ε δ u v).mp hR⟩
  · rintro ⟨⟨hS,h3⟩,h2,hR⟩
    exact ⟨fun i => (actual_signed_local_normalization (p i) p ε δ u v).mpr (hS i),
      (actual_signed_local_normalization 3 p ε δ u v).mpr h3,
      (actual_signed_local_normalization 2 p ε δ u v).mpr h2,
      (actual_signed_real_normalization p ε δ u v).mpr hR⟩

end ActualTwoDescentSignedAllBadNormalization318
