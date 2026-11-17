module
public import ActualTwoDescentComparisonCardinality318
public section
noncomputable section
namespace ActualTwoDescentSignedComparisons318
open ActualTwoDescentComparisonCardinality318 ActualTwoDescentLocalClassification318
open ActualTwoDescentFiniteConclusion318 ActualTwoDescentZeroSumCompletion318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentThreeSymbol318
open ActualTwoDescentTorsionComparison318 ActualTwoDescentIncidence318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Multiplication by the second torsion class (3,-l) removes a negative
second-coordinate sign and toggles delta and every support valuation. -/
def toggle (ε : ZMod 2) (v : Option U → ZMod 2) := v+ε • ones (Option U)
lemma toggle_twice (ε : ZMod 2) (v : Option U → ZMod 2) : toggle ε (toggle ε v)=v := by
  funext i
  change (v i+ε*1)+ε*1=v i
  ring
lemma bit_toggle_twice (δ ε : ZMod 2) : (δ+ε)+ε=δ := by ring

def signedCode (p : Option U → ℕ) (ε δ : ZMod 2) (u v : Option U → ZMod 2)
    (i : Option U) : Signature :=
  ((u i,δ*lambda p i+(edges p *ᵥ u) i),(v i,ε*parity p i+(edges p *ᵥ v) i))

/-- The sign normalization is the literal addition of the retained second
torsion signature, including its minus-one unit bit. -/
theorem actual_signed_normalization (p : Option U → ℕ) (ε δ : ZMod 2)
    (u v : Option U → ZMod 2) (i : Option U) :
    localCode p (δ+ε) u (toggle ε v) i=signedCode p ε δ u v i+ε • torsionTwo p i := by
  have hE : (edges p *ᵥ toggle ε v) i=(edges p *ᵥ v) i+ε*row p i := by
    rw [toggle,Matrix.mulVec_add,Matrix.mulVec_smul]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,ones,mul_one,row]
  apply Prod.ext
  · apply Prod.ext
    · change u i=u i+ε*0
      ring
    · change (δ+ε)*lambda p i+(edges p *ᵥ u) i=
        δ*lambda p i+(edges p *ᵥ u) i+ε*lambda p i
      ring
  · apply Prod.ext
    · change v i+ε*1=v i+ε*1
      rfl
    · change (edges p *ᵥ toggle ε v) i=
        ε*parity p i+(edges p *ᵥ v) i+ε*(parity p i+row p i)
      rw [hE]
      ring

/-- Signed coordinate comparisons are normalized using the actual torsion
operation above. This space is not asserted to equal the elliptic Selmer
group; its realization by local curve points remains a separate obligation. -/
abbrev SignedComparisonSpace (p : Option U → ℕ) :=
  {x : ZMod 2 × ZMod 2 × (Option U → ZMod 2) × (Option U → ZMod 2) //
    Admissible p (x.2.1+x.1) x.2.2.1 (toggle x.1 x.2.2.2)}

def actual_signed_comparison_equiv (p : Option U → ℕ) :
    SignedComparisonSpace p ≃ ZMod 2 × ComparisonSpace p where
  toFun x := (x.val.1,⟨(x.val.2.1+x.val.1,x.val.2.2.1,toggle x.val.1 x.val.2.2.2),x.property⟩)
  invFun x := ⟨(x.1,x.2.val.1+x.1,x.2.val.2.1,toggle x.1 x.2.val.2.2),by
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

/-- Eight signed comparison classes, derived from the actual coefficient
classification and literal torsion normalization, not assumed as a Selmer
rank. No global point-existence conclusion follows from this alone. -/
theorem actual_signed_comparison_card (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (h0 : beta none=0) (b : U) (hb : beta (some b)=1) :
    Nat.card (SignedComparisonSpace p)=8 := by
  rw [Nat.card_congr (actual_signed_comparison_equiv p),Nat.card_prod,
    actual_comparison_card p hp2 hp3 a beta N C h0 b hb]
  norm_num [Nat.card_eq_fintype_card]

end ActualTwoDescentSignedComparisons318
