module
public import RealMultiples318
public section
noncomputable section
open NumberField ConcreteG8Domain LocalGenerator318 ActualQuadraticEmbeddings318
namespace OddProductHeight318
set_option maxHeartbeats 0
variable {ι : Type*}

/-- Repeated labels are allowed: the finite set indexes occurrences,
not distinct values of the integer labels. -/
lemma multiple_height_product (s:Finset ι) (n:ι→ℤ) (hn:∀i∈s,n i≠0)
    (hf:∀w:FinitePlace K,
      (∀i∈s,w (((n i) • P).xRep 0)≤1) ∨ (∀i∈s,1≤w (((n i) • P).xRep 0))) :
    NumberField.absLogHeight₁ (∏i∈s,((n i) • P).xRep 0)=
      ∑i∈s,GlobalSaturationHeight318.xHeight ((n i) • P) := by
  apply ProductHeight318.absolute_height_product s (fun i=>((n i) • P).xRep 0) hf
  intro σ i hi
  exact RealMultiples318.multiple_P_abscissa_gt_one σ (n i) (hn i hi)

/-- The precise source odd-label product-height statement, retaining only
the actual finite-place common-sign input owned by the local subgroup lane. -/
theorem odd_multiple_height_product (s:Finset ι) (n:ι→ℤ) (hn:∀i∈s,Odd (n i))
    (hf:∀w:FinitePlace K,
      (∀i∈s,w (((n i) • P).xRep 0)≤1) ∨ (∀i∈s,1≤w (((n i) • P).xRep 0))) :
    NumberField.absLogHeight₁ (∏i∈s,((n i) • P).xRep 0)=
      ∑i∈s,GlobalSaturationHeight318.xHeight ((n i) • P) := by
  apply multiple_height_product s n _ hf
  intro i hi hz
  have hh := hn i hi
  rw [hz] at hh
  norm_num at hh

lemma product_positive_at_real (s:Finset ι) (n:ι→ℤ) (hn:∀i∈s,n i≠0) (σ:K→+*ℝ) :
    0<σ (∏i∈s,((n i) • P).xRep 0) := by
  rw [map_prod]
  exact Finset.prod_pos (fun i hi=>lt_trans (by norm_num) (RealMultiples318.multiple_P_abscissa_gt_one σ (n i) (hn i hi)))

lemma real_part_pos_of_embeddings (x:K)
    (hp:0<positiveEmbedding x) (hm:0<negativeEmbedding x) : 0<(x.re:ℝ) := by
  rcases x with ⟨u,v⟩
  change 0<positiveEmbedding (pair u v) at hp
  change 0<negativeEmbedding (pair u v) at hm
  simp only [positiveEmbedding,negativeEmbedding,realEmbedding_pair,mul_neg] at hp hm
  change 0<(u:ℝ)
  linarith

/-- This is positivity of the actual product's rational coefficient C0,
not of a norm of that product. It also includes the empty product. -/
lemma product_real_part_positive (s:Finset ι) (n:ι→ℤ) (hn:∀i∈s,n i≠0) :
    0<(∏i∈s,((n i) • P).xRep 0).re := by
  have hh := real_part_pos_of_embeddings (∏i∈s,((n i) • P).xRep 0)
    (product_positive_at_real s n hn positiveEmbedding) (product_positive_at_real s n hn negativeEmbedding)
  exact_mod_cast hh

#print axioms multiple_height_product
#print axioms odd_multiple_height_product
#print axioms product_positive_at_real
#print axioms real_part_pos_of_embeddings
#print axioms product_real_part_positive
end OddProductHeight318
