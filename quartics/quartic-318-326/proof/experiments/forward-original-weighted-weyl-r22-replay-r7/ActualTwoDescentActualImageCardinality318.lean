module
public import ActualTwoDescentActualImageEquivalence318
public section
noncomputable section
namespace ActualTwoDescentActualImageCardinality318
open ActualTwoDescentActualLocalClassBound318 ActualTwoDescentActualImageEquivalence318
open ActualTwoDescentComparisonCardinality318 ActualTwoDescentFiniteConclusion318
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Actual positive normalized local-image intersection at the support
primes and3, not a renamed formal matrix-comparison space. -/
abbrev ActualImageSpace (p : Option U → ℕ) [∀ i, Fact (p i).Prime] :=
  {x : ZMod 2 × (Option U → ZMod 2) × (Option U → ZMod 2) //
    BadLocallyRepresented p x.1 x.2.1 x.2.2}

/-- The equivalence preserves all representative coordinates literally.
Its forward direction uses actual local-image necessity; its inverse
constructs actual local points, not only residue-symbol equalities. -/
def actual_image_comparison_equiv (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N) :
    ActualImageSpace p ≃ ComparisonSpace p where
  toFun x := ⟨x.val,(actual_bad_local_image_equivalence p hd hp2 hp3 a beta N C _ _ _).mp x.property⟩
  invFun x := ⟨x.val,(actual_bad_local_image_equivalence p hd hp2 hp3 a beta N C _ _ _).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exactly four positive normalized ACTUAL local classes at the treated
bad places. This is not a Selmer-dimension or rational-point theorem. -/
theorem actual_image_card_four (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (h0 : beta none=0) (b : U) (hb : beta (some b)=1) :
    Nat.card (ActualImageSpace p)=4 := by
  rw [Nat.card_congr (actual_image_comparison_equiv p hd hp2 hp3 a beta N C)]
  exact actual_comparison_card p hp2 hp3 a beta N C h0 b hb

end ActualTwoDescentActualImageCardinality318
