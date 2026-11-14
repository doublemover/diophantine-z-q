module
public import ActualTwoDescentAuxiliaryTypes318
public section
noncomputable section
namespace ActualTwoDescentEdgeAction318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentSignReciprocity318
open ActualTwoDescentMatrixCompletion318 ActualTwoDescentAuxiliaryTypes318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact row action of the actual prime-symbol Laplacian, retaining the
same excluded self-edge and plus sign in characteristic two. -/
lemma actual_edge_action (p : ι → ℕ) (v : ι → ZMod 2) (i : ι) :
    (laplacian p *ᵥ v) i=∑ j, edges p i j*(v j+v i) := by
  simp only [laplacian,Matrix.add_mulVec,Pi.add_apply]
  have hd : (Matrix.diagonal (fun i => ∑ j, edges p i j) *ᵥ v) i=
      (∑ j, edges p i j)*v i := by simp [Matrix.mulVec,dotProduct]
  rw [hd]
  simp only [Matrix.mulVec,dotProduct,mul_add,Finset.sum_add_distrib,Finset.sum_mul]

lemma actual_edge_reciprocity (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2)
    (i j : ι) (hne : i ≠ j) :
    edges p i j+edges p j i=parity p i*parity p j := by
  have h := actual_symbol_reciprocity (p j) (p i) (hp2 j) (hp2 i)
    (fun h => hne (hd h).symm)
  simpa [edges,parity,hne,Ne.symm hne,mul_comm] using h

lemma actual_edge_reverse_zero (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2)
    (i j : ι) (hi : parity p i=0) : edges p i j=edges p j i := by
  by_cases he : i=j
  · subst j; rfl
  · apply eq_of_add_zero
    rw [actual_edge_reciprocity p hd hp2 i j he,hi,zero_mul]

end ActualTwoDescentEdgeAction318
