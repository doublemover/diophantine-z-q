module
public import ActualCanonicalHeight318
public section
noncomputable section
open NumberField ConcreteG8Domain
namespace ProductHeight318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable {ι : Type*}

lemma max_prod_of_common_sign (s:Finset ι) (f:ι→ℝ) (h0:∀i∈s,0≤f i)
    (hs:(∀i∈s,f i≤1) ∨ (∀i∈s,1≤f i)) :
    max (∏i∈s,f i) 1=∏i∈s,max (f i) 1 := by
  rcases hs with hlo|hhi
  · rw [max_eq_right (Finset.prod_le_one₀ h0 hlo)]
    symm
    apply Finset.prod_eq_one
    intro i hi
    exact max_eq_right (hlo i hi)
  · rw [max_eq_left (Finset.one_le_prod₀ hhi)]
    apply Finset.prod_congr rfl
    intro i hi
    exact (max_eq_left (hhi i hi)).symm

lemma finite_local_product (s:Finset ι) (x:ι→K) (w:FinitePlace K)
    (hs:(∀i∈s,w (x i)≤1) ∨ (∀i∈s,1≤w (x i))) :
    max (w (∏i∈s,x i)) 1=∏i∈s,max (w (x i)) 1 := by
  rw [map_prod]
  exact max_prod_of_common_sign s (fun i=>w (x i)) (fun i _=>apply_nonneg w _) hs

lemma infinite_local_product (s:Finset ι) (x:ι→K) (w:InfinitePlace K)
    (hs:∀(σ:K→+*ℝ),∀i∈s,1<σ (x i)) :
    max (w (∏i∈s,x i)) 1=∏i∈s,max (w (x i)) 1 := by
  obtain ⟨σ,hσ⟩ := ActualQuadraticEmbeddings318.infinite_place_real_value w
  have hhi (i) (hi:i∈s) : 1≤w (x i) := by
    rw [hσ,abs_of_pos (lt_trans (by norm_num) (hs σ i hi))]
    exact (hs σ i hi).le
  rw [map_prod]
  exact max_prod_of_common_sign s (fun i=>w (x i)) (fun i _=>apply_nonneg w _) (Or.inr hhi)

lemma relative_height_product (s:Finset ι) (x:ι→K)
    (hf:∀w:FinitePlace K,(∀i∈s,w (x i)≤1) ∨ (∀i∈s,1≤w (x i)))
    (ha:∀(σ:K→+*ℝ),∀i∈s,1<σ (x i)) :
    Height.mulHeight₁ (∏i∈s,x i)=∏i∈s,Height.mulHeight₁ (x i) := by
  rw [NumberField.mulHeight₁_eq]
  simp_rw [infinite_local_product s x _ ha,finite_local_product s x _ (hf _),←Finset.prod_pow]
  rw [Finset.prod_comm,finprod_prod_comm s (fun (w:FinitePlace K) (i:ι)=>max (w (x i)) 1)
    (fun i _=>FiniteHeightEquiv.finite_max_support (x i)),←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact (NumberField.mulHeight₁_eq (x i)).symm

/-- Exact actual absolute-height additivity for an arbitrary finite family.
The finite-place common weak signs and real >1 hypotheses are explicit. -/
theorem absolute_height_product (s:Finset ι) (x:ι→K)
    (hf:∀w:FinitePlace K,(∀i∈s,w (x i)≤1) ∨ (∀i∈s,1≤w (x i)))
    (ha:∀(σ:K→+*ℝ),∀i∈s,1<σ (x i)) :
    NumberField.absLogHeight₁ (∏i∈s,x i)=∑i∈s,NumberField.absLogHeight₁ (x i) := by
  simp_rw [AbsoluteHeightNormalization318.absLogHeight_eq_half_relative]
  rw [relative_height_product s x hf ha,Real.log_prod (fun i _=>(Height.mulHeight₁_pos (x i)).ne'),Finset.sum_div]

#print axioms max_prod_of_common_sign
#print axioms finite_local_product
#print axioms infinite_local_product
#print axioms relative_height_product
#print axioms absolute_height_product
end ProductHeight318
