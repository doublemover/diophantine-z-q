module
public import ActualTwoDescentStrippedSymbols318
public section
noncomputable section
namespace ActualTwoDescentTorsionComparison318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentThreeSymbol318
open ActualTwoDescentEdgeAction318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Signature := (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)
def row (p : ι → ℕ) (i : ι) : ZMod 2 := ∑ j, edges p i j
/-- Valuation and stripped-unit bits of the two original descent coordinates.
The stripped-unit interpretation is proved separately, not assumed to be a
statement about the full local image of an elliptic curve. -/
def localCode (p : ι → ℕ) (δ : ZMod 2) (u v : ι → ZMod 2) (i : ι) : Signature :=
  ((u i,δ*lambda p i+(edges p *ᵥ u) i),(v i,(edges p *ᵥ v) i))
/-- The signatures of the two retained torsion classes (l,1) and (3,-l). -/
def torsionOne (p : ι → ℕ) (i : ι) : Signature := ((1,row p i),(0,0))
def torsionTwo (p : ι → ℕ) (i : ι) : Signature := ((0,lambda p i),(1,parity p i+row p i))

lemma actual_row_action (p : ι → ℕ) (u : ι → ZMod 2) (i : ι) :
    (laplacian p *ᵥ u) i=(edges p *ᵥ u) i+row p i*u i := by
  rw [actual_edge_action]
  simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,Matrix.mulVec,dotProduct,row]

/-- The two torsion valuation vectors are independent, so matching the
local signatures forces the torsion coefficients to equal u_i and v_i. -/
lemma actual_torsion_coefficients (p : ι → ℕ) (δ : ZMod 2) (u v : ι → ZMod 2)
    (i : ι) (a b : ZMod 2)
    (h : localCode p δ u v i=a • torsionOne p i+b • torsionTwo p i) :
    a=u i ∧ b=v i := by
  have h1 := congrArg (fun s : Signature => s.1.1) h
  have h2 := congrArg (fun s : Signature => s.2.1) h
  constructor
  · simpa [localCode,torsionOne,torsionTwo,smul_eq_mul] using h1.symm
  · simpa [localCode,torsionOne,torsionTwo,smul_eq_mul] using h2.symm

/-- Actual torsion comparison at a support prime is exactly the two
finite row equations, with the original coordinate order and signs. -/
theorem actual_torsion_comparison_iff (p : ι → ℕ) (δ : ZMod 2)
    (u v : ι → ZMod 2) (i : ι) :
    (∃ a b : ZMod 2, localCode p δ u v i=a • torsionOne p i+b • torsionTwo p i) ↔
      (laplacian p *ᵥ u) i+lambda p i*v i=δ*lambda p i ∧
      (laplacian p *ᵥ v) i+parity p i*v i=0 := by
  rw [actual_row_action,actual_row_action]
  constructor
  · rintro ⟨a,b,h⟩
    obtain ⟨rfl,rfl⟩ := actual_torsion_coefficients p δ u v i a b h
    have h1 := congrArg (fun s : Signature => s.1.2) h
    have h2 := congrArg (fun s : Signature => s.2.2) h
    change δ*lambda p i+(edges p *ᵥ u) i=u i*row p i+v i*lambda p i at h1
    change (edges p *ᵥ v) i=u i*0+v i*(parity p i+row p i) at h2
    constructor
    · linear_combination h1
    · linear_combination h2
  · rintro ⟨h1,h2⟩
    refine ⟨u i,v i,?_⟩
    apply Prod.ext
    · apply Prod.ext
      · simp [localCode,torsionOne,torsionTwo,smul_eq_mul]
      · change δ*lambda p i+(edges p *ᵥ u) i=u i*row p i+v i*lambda p i
        linear_combination h1
    · apply Prod.ext
      · simp [localCode,torsionOne,torsionTwo,smul_eq_mul]
      · change (edges p *ᵥ v) i=u i*0+v i*(parity p i+row p i)
        linear_combination h2

end ActualTwoDescentTorsionComparison318
