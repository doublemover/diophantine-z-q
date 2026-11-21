module
public import Mathlib
public section
noncomputable section
namespace ActualTZFiniteProductNearOne318
open scoped BigOperators

/-- A finite product may have arbitrary complex signs/phases. Its
distance to 1 is bounded by the ordinary exponential of the sum
of the local absolute differences. -/
theorem product_near_one {J : Type*} (S : Finset J) (b : J→ℂ) (e : J→ℝ)
    (he : ∀ j∈S,‖b j-1‖≤e j) :
    ‖(∏ j∈S,b j)-1‖≤Real.exp (∑ j∈S,e j)-1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    have h₀ := he j (Finset.mem_insert_self _ _)
    have hS (j' : J) (hj' : j'∈S) := he j' (Finset.mem_insert_of_mem hj')
    have e₀ := (norm_nonneg (b j-1)).trans h₀
    have H := ih hS
    have hb : ‖b j‖≤1+e j := by
      have h := norm_add_le (1:ℂ) (b j-1)
      have e : (1:ℂ)+(b j-1)=b j := by ring
      rw [e,norm_one] at h
      linarith
    rw [Finset.prod_insert hj,Finset.sum_insert hj]
    let P := ∏ j∈S,b j
    let B := ∑ j∈S,e j
    change ‖b j*P-1‖ ≤ Real.exp (e j+B)-1
    have E : b j*P-1=b j*(P-1)+(b j-1) := by ring
    calc
      _ ≤ ‖b j*(P-1)‖+‖b j-1‖ := by rw [E]; exact norm_add_le _ _
      _ ≤ (1+e j)*(Real.exp B-1)+e j := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul hb H (norm_nonneg _) (by linarith)) h₀
      _ = (1+e j)*Real.exp B-1 := by ring
      _ ≤ _ := by
        rw [Real.exp_add]
        have hExp : 1+e j≤Real.exp (e j) := by
          simpa only [add_comm 1 (e j)] using Real.add_one_le_exp (e j)
        exact sub_le_sub_right (mul_le_mul_of_nonneg_right hExp (Real.exp_pos B).le) 1

end ActualTZFiniteProductNearOne318
