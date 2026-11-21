module
public import Mathlib
public section
noncomputable section
namespace ActualTZProductResidueDominance318
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {F : Type*} [DecidableEq F]

/-- Independent residue masses on potentially DIFFERENT per-axis
finite sets, with only bounded likelihood ratios to uniform. No
assumption that residue masses themselves are uniform. -/
theorem subbox_mass (S : Fin n→Finset F) (T : Finset (Fin n→F))
    (hT : T⊆Fintype.piFinset S) (m : Fin n→F→ℚ≥0) (A : ℚ≥0)
    (hM : ∀ i x,x∈S i→m i x≤A/((S i).card:ℚ≥0)) :
    (∑ z∈T,∏ i : Fin n,m i (z i))≤
      A^n*((T.card:ℚ≥0)/(∏ i : Fin n,((S i).card:ℚ≥0))) := by
  have H : (∏ i : Fin n,A/((S i).card:ℚ≥0))=
      A^n/(∏ i : Fin n,((S i).card:ℚ≥0)) := by
    simp only [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  calc
    _ ≤ ∑ _z∈T,∏ i : Fin n,A/((S i).card:ℚ≥0) := by
      apply Finset.sum_le_sum
      intro z hz
      exact Finset.prod_le_prod₀ (fun _ _=>zero_le _) (fun i _=>
        hM i (z i) (Fintype.mem_piFinset.mp (hT hz) i))
    _ = _ := by rw [H,Finset.sum_const,nsmul_eq_mul,mul_div_assoc]; ac_rfl

end ActualTZProductResidueDominance318
