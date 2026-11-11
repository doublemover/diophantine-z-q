module
public import ActualTwoDescentEdgeAction318
public section
noncomputable section
namespace ActualTwoDescentSmallPattern318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentSupportParity318
open ActualTwoDescentThreeSymbol318 ActualTwoDescentIncidence318
open ActualTwoDescentAuxiliaryTypes318 ActualTwoDescentEdgeAction318
open ActualTwoDescentMatrixCompletion318 ActualTwoDescentZeroSumCompletion318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

abbrev BetaIndex (d : ℕ) := Option (Fin d)
abbrev CoreIndex (d : ℕ) := BetaIndex d ⊕ Fin d
abbrev Index (d : ℕ) := Option (CoreIndex d)
def bIndex {d : ℕ} (b : BetaIndex d) : Index d := some (Sum.inl b)
def iIndex {d : ℕ} (i : Fin d) : Index d := some (Sum.inr i)
def beta (d : ℕ) : Index d → ZMod 2
  | none => 0
  | some (Sum.inl _) => 1
  | some (Sum.inr _) => 0

def selector (d : ℕ) : Index d → ZMod 2
  | none => 1
  | some (Sum.inl none) => 1
  | _ => 0

/-- The precise small-support symbol prescriptions. The two directions
are NOT both assumed: reverse symbols are derived by actual reciprocity. -/
structure Pattern (d : ℕ) (p : Index d → ℕ) : Prop where
  cross : ∀ b i, edges p (bIndex b) (iIndex i)=incidence d b i
  internal : ∀ i j, edges p (iIndex i) (iIndex j)=0
  to_q0 : ∀ i, edges p (iIndex i) none=0
  q0_at_beta : ∀ b, edges p (bIndex b) none=∑ i, incidence d b i
  typeI : ∀ i, (p (iIndex i) : ZMod 12)=1
  typeQ : (p none : ZMod 12)=7

lemma selector_sum (d : ℕ) : (∑ i, selector d i)=0 := by
  norm_num [selector,Fintype.sum_option,Fintype.sum_sum_type]
lemma selector_beta (d : ℕ) : dotProduct (selector d) (beta d)=1 := by
  simp [dotProduct,selector,beta,Fintype.sum_option,Fintype.sum_sum_type]
lemma selector_on_beta_sum (d : ℕ) : (∑ b, selector d (bIndex b))=1 := by
  simp [selector,bIndex,Fintype.sum_option]
lemma incidence_column_sum (d : ℕ) (i : Fin d) : (∑ b, incidence d b i)=0 := by
  norm_num [incidence,Fintype.sum_option]
lemma incidence_all_sum (d : ℕ) : (∑ b, ∑ i, incidence d b i)=0 := by
  simpa [Matrix.mulVec,dotProduct,ones] using actual_incidence_total d (ones (Fin d))

lemma beta_row_B (d : ℕ) (p : Index d → ℕ) (b : BetaIndex d) :
    (laplacian p *ᵥ beta d) (bIndex b)=
      edges p (bIndex b) none+∑ i, edges p (bIndex b) (iIndex i) := by
  rw [actual_edge_action]
  simp [beta,bIndex,iIndex,Fintype.sum_option,Fintype.sum_sum_type,add_comm]
lemma beta_row_I (d : ℕ) (p : Index d → ℕ) (i : Fin d) :
    (laplacian p *ᵥ beta d) (iIndex i)=∑ b, edges p (iIndex i) (bIndex b) := by
  rw [actual_edge_action]
  simp [beta,bIndex,iIndex,Fintype.sum_option,Fintype.sum_sum_type]
lemma beta_row_Q (d : ℕ) (p : Index d → ℕ) :
    (laplacian p *ᵥ beta d) none=∑ b, edges p none (bIndex b) := by
  rw [actual_edge_action]
  simp [beta,bIndex,iIndex,Fintype.sum_option,Fintype.sum_sum_type]

lemma actual_parity_I (d : ℕ) (p : Index d → ℕ) (H : Pattern d p) (i : Fin d) :
    parity p (iIndex i)=0 := (actual_type_one _ (H.typeI i)).1
lemma actual_lambda_I (d : ℕ) (p : Index d → ℕ) (H : Pattern d p) (i : Fin d) :
    lambda p (iIndex i)=0 := (actual_type_one _ (H.typeI i)).2
lemma actual_parity_Q (d : ℕ) (p : Index d → ℕ) (H : Pattern d p) :
    parity p none=1 := (actual_type_seven _ H.typeQ).1
lemma actual_lambda_Q (d : ℕ) (p : Index d → ℕ) (H : Pattern d p) :
    lambda p none=1 := (actual_type_seven _ H.typeQ).2

lemma actual_beta_parity_sum (d : ℕ) (p : Index d → ℕ) [∀ i, Fact (p i).Prime]
    (hp2 : ∀ i, p i ≠ 2) (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) (H : Pattern d p) :
    (∑ b, parity p (bIndex b))=0 := by
  have ht := actual_total_parity p hp2 hn
  have h : parity p none+((∑ b, parity p (bIndex b))+(∑ i, parity p (iIndex i)))=1 := by
    simpa only [Fintype.sum_option,Fintype.sum_sum_type] using ht
  have hI : (∑ i, parity p (iIndex i))=0 :=
    Finset.sum_eq_zero (fun i _ => actual_parity_I d p H i)
  rw [actual_parity_Q d p H,hI,add_zero] at h
  exact add_left_cancel (h.trans (add_zero 1).symm)

lemma actual_beta_lambda_sum (d : ℕ) (p : Index d → ℕ) [∀ i, Fact (p i).Prime]
    (hp3 : ∀ i, p i ≠ 3) (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) (H : Pattern d p) :
    (∑ b, lambda p (bIndex b))=1 := by
  have ht := actual_lambda_sum p hp3 hn
  have h : lambda p none+((∑ b, lambda p (bIndex b))+(∑ i, lambda p (iIndex i)))=0 := by
    simpa only [Fintype.sum_option,Fintype.sum_sum_type] using ht
  have hI : (∑ i, lambda p (iIndex i))=0 :=
    Finset.sum_eq_zero (fun i _ => actual_lambda_I d p H i)
  rw [actual_lambda_Q d p H,hI,add_zero] at h
  exact (eq_of_add_zero _ _ h).symm

lemma actual_cross_reverse (d : ℕ) (p : Index d → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (H : Pattern d p)
    (i : Fin d) (b : BetaIndex d) : edges p (iIndex i) (bIndex b)=incidence d b i := by
  rw [actual_edge_reverse_zero p hd hp2 _ _ (actual_parity_I d p H i),H.cross]

/-- The actual beta-indicator row condition is discharged from the
chosen incidence pattern, not retained as an abstract kernel premise. -/
theorem actual_small_beta_kernel (d : ℕ) (p : Index d → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) (H : Pattern d p) :
    laplacian p *ᵥ beta d=0 := by
  have hQB (b : BetaIndex d) :
      edges p none (bIndex b)=(∑ i, incidence d b i)+parity p (bIndex b) := by
    apply eq_add_of_add_eq
    rw [←H.q0_at_beta b,
      actual_edge_reciprocity p hd hp2 none (bIndex b) (by simp [bIndex]),
      actual_parity_Q d p H,one_mul]
  funext k
  cases k with
  | none =>
    rw [beta_row_Q]
    simp_rw [hQB]
    rw [Finset.sum_add_distrib,incidence_all_sum,actual_beta_parity_sum d p hp2 hn H,add_zero]
  | some k =>
    cases k with
    | inl b =>
      change (laplacian p *ᵥ beta d) (bIndex b)=0
      rw [beta_row_B,H.q0_at_beta]
      simp_rw [H.cross]
      exact actual_two_add _
    | inr i =>
      change (laplacian p *ᵥ beta d) (iIndex i)=0
      rw [beta_row_I]
      simp_rw [actual_cross_reverse d p hd hp2 H]
      exact incidence_column_sum d i

end ActualTwoDescentSmallPattern318
