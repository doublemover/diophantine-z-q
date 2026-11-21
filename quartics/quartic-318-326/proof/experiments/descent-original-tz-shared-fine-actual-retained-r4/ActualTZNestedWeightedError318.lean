module
public import Mathlib
public section
noncomputable section
namespace ActualTZNestedWeightedError318
open scoped BigOperators

variable {G K : Type*} [Fintype G] [Fintype K]

theorem sub_bound (m : G→ℝ) (w : G→K→ℝ)
    (F D : G→K→ℝ) (E : ℝ) (hm : ∀ z : G, (0:ℝ) ≤ m z) (hw : ∀ z r,0≤w z r)
    (hE : ∀ z r,0<w z r→|F z r-D z r|≤E) :
    |(∑ z : G,m z*(∑ r : K,w z r*F z r))-
      (∑ z : G,m z*(∑ r : K,w z r*D z r))|≤
      E*(∑ z : G,m z*(∑ r : K,w z r)) := by
  simp only [←Finset.sum_sub_distrib,←mul_sub]
  calc
    _ ≤ ∑ z : G,m z*(∑ r : K,w z r*|F z r-D z r|) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro z _
      rw [abs_mul,abs_of_nonneg (hm z)]
      apply mul_le_mul_of_nonneg_left _ (hm z)
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul,abs_of_nonneg (hw z r)]
    _ ≤ ∑ z : G,m z*(∑ r : K,w z r*E) := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (hm z)
      apply Finset.sum_le_sum
      intro r _
      rcases (hw z r).eq_or_lt with he|hp
      · simp only [←he,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (hE z r hp) hp.le
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro r _
      ring

theorem unit_sub_bound (m : G→ℝ) (w : G→K→ℝ)
    (F D : G→K→ℝ) (E : ℝ) (hm : ∀ z : G, (0:ℝ) ≤ m z) (hw : ∀ z r,0≤w z r) (h0 : 0≤E)
    (hE : ∀ z r,0<w z r→|F z r-D z r|≤E)
    (hM : (∑ z : G,m z*(∑ r : K,w z r))≤1) :
    |(∑ z : G,m z*(∑ r : K,w z r*F z r))-
      (∑ z : G,m z*(∑ r : K,w z r*D z r))|≤E :=
  (sub_bound m w F D E hm hw hE).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hM h0)

end ActualTZNestedWeightedError318
