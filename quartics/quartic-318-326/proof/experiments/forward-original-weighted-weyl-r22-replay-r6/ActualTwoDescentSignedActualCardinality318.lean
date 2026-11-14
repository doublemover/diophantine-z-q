module
public import ActualTwoDescentSignedAllBadNormalization318
public section
noncomputable section
namespace ActualTwoDescentSignedActualCardinality318
open ActualTwoDescentSignedAllBadNormalization318 ActualTwoDescentAllBadCardinality318
open ActualTwoDescentSignedComparisons318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentPrimeMonomials318
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

abbrev SignedActualSpace (p : Option U → ℕ) [∀ i, Fact (p i).Prime] :=
  {x : ZMod 2 × ZMod 2 × (Option U → ZMod 2) × (Option U → ZMod 2) //
    SignedAllBadRepresented p x.1 x.2.1 x.2.2.1 x.2.2.2}

/-- A genuine local-point normalization equivalence, not the earlier
formal signature normalization. Its inverse constructs signed points by
the actual torsion translation at every treated place. -/
def actual_signed_positive_equiv (p : Option U → ℕ) [∀ i, Fact (p i).Prime] :
    SignedActualSpace p ≃ ZMod 2 × AllBadSpace p where
  toFun x := (x.val.1,⟨(x.val.2.1+x.val.1,x.val.2.2.1,toggle x.val.1 x.val.2.2.2),
    (actual_signed_all_bad_normalization p _ _ _ _).mp x.property⟩)
  invFun x := ⟨(x.1,x.2.val.1+x.1,x.2.val.2.1,toggle x.1 x.2.val.2.2),by
    apply (actual_signed_all_bad_normalization p _ _ _ _).mpr
    simpa only [bit_toggle_twice,toggle_twice] using x.2.property⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨ε,δ,u,v⟩,H⟩
    change (ε,(δ+ε)+ε,u,toggle ε (toggle ε v))=(ε,δ,u,v)
    rw [bit_toggle_twice,toggle_twice]
  right_inv x := by
    rcases x with ⟨ε,⟨⟨δ,u,v⟩,H⟩⟩
    apply Prod.ext rfl
    apply Subtype.ext
    change ((δ+ε)+ε,u,toggle ε (toggle ε v))=(δ,u,v)
    rw [bit_toggle_twice,toggle_twice]

/-- Exactly eight SIGNED actual local-image classes at all bad places and
infinity. Good-prime sufficiency and full global Selmer identification are
not implied by this finite representative-space count. -/
theorem actual_signed_image_card_eight (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (hb : (monomial p beta : ZMod 8)=1)
    (h0 : beta none=0) (b : U) (hb1 : beta (some b)=1) :
    Nat.card (SignedActualSpace p)=8 := by
  rw [Nat.card_congr (actual_signed_positive_equiv p),Nat.card_prod,
    actual_all_bad_card_four p hd hp2 hp3 a beta N C hb h0 b hb1]
  norm_num [Nat.card_eq_fintype_card]

end ActualTwoDescentSignedActualCardinality318
