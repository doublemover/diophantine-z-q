module
public import ActualTwoDescentBetaThetaFamily318
public section
noncomputable section
namespace ActualTwoDescentExtendedVectors318
open ActualTwoDescentOldCorePreservation318 ActualTwoDescentPrimeLaplacian318
open ActualTwoDescentEdgeAction318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000
variable {U J : Type*} [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]

def extend (v : Option U → ZMod 2) : Option (U ⊕ J) → ZMod 2
  | none => v none
  | some (Sum.inl i) => v (some i)
  | some (Sum.inr _) => 0
lemma extend_old (v : Option U → ZMod 2) (i : Option U) :
    (extend v : Option (U ⊕ J) → ZMod 2) (oldEmbedding i)=v i := by
  cases i <;> rfl
lemma restrictedSelector_extend (v : Option U → ZMod 2) :
    restrictedSelector (extend v : Option (U ⊕ J) → ZMod 2)=v := by
  funext i
  exact extend_old v i
lemma extend_sum (v : Option U → ZMod 2) :
    (∑ i : Option (U ⊕ J), extend v i)=∑ i, v i := by
  simp only [Fintype.sum_option,Fintype.sum_sum_type,extend,Finset.sum_const_zero,add_zero]
lemma extend_dot (v w : Option U → ZMod 2) :
    dotProduct (extend v : Option (U ⊕ J) → ZMod 2) (extend w)=dotProduct v w := by
  simp only [dotProduct,Fintype.sum_option,Fintype.sum_sum_type,extend,mul_zero,
    Finset.sum_const_zero,add_zero]

/-- Exact old-row action after adjoining theta, with the actual cross
row-sum term retained rather than silently discarded. -/
lemma actual_old_row_extension (p : Option (U ⊕ J) → ℕ) (v : Option U → ZMod 2) (i : Option U) :
    (laplacian p *ᵥ extend v) (oldEmbedding i)=
      (laplacian (restricted p) *ᵥ v) i+
        (∑ j : J, edges p (oldEmbedding i) (some (Sum.inr j)))*v i := by
  rw [actual_edge_action,actual_edge_action]
  simp_rw [actual_restricted_edges]
  simp only [Fintype.sum_option,Fintype.sum_sum_type,extend_old,extend,oldEmbedding,zero_add]
  rw [Finset.sum_mul]
  ring

lemma actual_theta_row_extension (p : Option (U ⊕ J) → ℕ)
    (v : Option U → ZMod 2) (hv : v none=0) (j : J) :
    (laplacian p *ᵥ extend v) (some (Sum.inr j))=
      ∑ i : U, edges p (some (Sum.inr j)) (some (Sum.inl i))*v (some i) := by
  rw [actual_edge_action]
  simp only [Fintype.sum_option,Fintype.sum_sum_type,extend,hv,zero_add,add_zero,mul_zero,
    Finset.sum_const_zero,zero_add]

/-- Actual beta-kernel preservation under adjoining theta is derived from
both directed mutual-square row sums, with beta zero on theta and q0. -/
theorem actual_extended_kernel (p : Option (U ⊕ J) → ℕ)
    (v : Option U → ZMod 2) (hv0 : v none=0) (hv : laplacian (restricted p) *ᵥ v=0)
    (hcross : ∀ i : U, (∑ j : J, edges p (some (Sum.inl i)) (some (Sum.inr j)))=0)
    (hnew : ∀ j : J, (∑ i : U, edges p (some (Sum.inr j)) (some (Sum.inl i))*v (some i))=0) :
    laplacian p *ᵥ extend v=0 := by
  funext i
  cases i with
  | none =>
    have h := actual_old_row_extension p v none
    simpa only [oldEmbedding,hv,Pi.zero_apply,hv0,mul_zero,add_zero] using h
  | some i =>
    cases i with
    | inl i =>
      have h := actual_old_row_extension p v (some i)
      simpa only [oldEmbedding,hv,Pi.zero_apply,hcross,zero_mul,add_zero] using h
    | inr j =>
      rw [actual_theta_row_extension p v hv0 j,hnew]
      rfl

end ActualTwoDescentExtendedVectors318
