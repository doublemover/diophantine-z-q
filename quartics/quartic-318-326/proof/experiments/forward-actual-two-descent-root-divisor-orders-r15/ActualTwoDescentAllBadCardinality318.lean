module
public import ActualTwoDescentAllBadEquivalence318
public section
noncomputable section
namespace ActualTwoDescentAllBadCardinality318
open ActualTwoDescentAllBadEquivalence318 ActualTwoDescentActualImageCardinality318
open ActualTwoDescentFiniteConclusion318 ActualTwoDescentPrimeMonomials318
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

abbrev AllBadSpace (p : Option U → ℕ) [∀ i, Fact (p i).Prime] :=
  {x : ZMod 2 × (Option U → ZMod 2) × (Option U → ZMod 2) // AllBadRepresented p x.1 x.2.1 x.2.2}

def actual_all_bad_image_equiv (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (hb : (monomial p beta : ZMod 8)=1) : AllBadSpace p ≃ ActualImageSpace p where
  toFun x := ⟨x.val,x.property.1⟩
  invFun x := ⟨x.val,(actual_all_bad_equivalence p hd hp2 hp3 a beta N C hb _ _ _).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Four positive normalized classes in the ACTUAL local image at every
bad prime and the real place. No global Selmer or rational-point conclusion. -/
theorem actual_all_bad_card_four (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (hb : (monomial p beta : ZMod 8)=1)
    (h0 : beta none=0) (b : U) (hb1 : beta (some b)=1) :
    Nat.card (AllBadSpace p)=4 := by
  rw [Nat.card_congr (actual_all_bad_image_equiv p hd hp2 hp3 a beta N C hb)]
  exact actual_image_card_four p hd hp2 hp3 a beta N C h0 b hb1

end ActualTwoDescentAllBadCardinality318
