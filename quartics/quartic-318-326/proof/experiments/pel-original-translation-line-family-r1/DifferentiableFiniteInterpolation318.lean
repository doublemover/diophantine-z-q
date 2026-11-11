module
public import AnalyticFiniteInterpolation318
public section
noncomputable section
namespace DifferentiableFiniteInterpolation318
open Polynomial
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma finite_sum (T : Finset I) (f : I → E → ℂ) (x : E)
    (hf : ∀ i ∈ T, DifferentiableAt ℂ (f i) x) :
    DifferentiableAt ℂ (fun w => ∑ i ∈ T, f i w) x := by
  classical
  revert hf
  induction T using Finset.induction_on with
  | empty => intro hf; simpa using (differentiableAt_const (0 : ℂ) : DifferentiableAt ℂ (fun _ : E => (0 : ℂ)) x)
  | @insert i T hi ih =>
      intro hf
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self _ _)).add
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma finite_product (T : Finset I) (f : I → E → ℂ) (x : E)
    (hf : ∀ i ∈ T, DifferentiableAt ℂ (f i) x) :
    DifferentiableAt ℂ (fun w => ∏ i ∈ T, f i w) x := by
  classical
  revert hf
  induction T using Finset.induction_on with
  | empty => intro hf; simpa using (differentiableAt_const (1 : ℂ) : DifferentiableAt ℂ (fun _ : E => (1 : ℂ)) x)
  | @insert i T hi ih =>
      intro hf
      simpa only [Finset.prod_insert hi] using
        (hf i (Finset.mem_insert_self _ _)).mul
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma product_coefficient (T : Finset I) (P : I → E → Polynomial ℂ) (x : E)
    (hP : ∀ i ∈ T, ∀ n, DifferentiableAt ℂ (fun w => (P i w).coeff n) x)
    (n : ℕ) : DifferentiableAt ℂ (fun w => (∏ i ∈ T, P i w).coeff n) x := by
  classical
  revert hP n
  induction T using Finset.induction_on with
  | empty => intro hP n; simpa using (differentiableAt_const ((1 : Polynomial ℂ).coeff n))
  | @insert i T hi ih =>
      intro hP n
      simp only [Finset.prod_insert hi]
      simp_rw [Polynomial.coeff_mul]
      apply finite_sum
      intro k hk
      exact (hP i (Finset.mem_insert_self _ _) k.1).mul
        (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)) k.2)

/-- Complex differentiability suffices for interpolation. This is the
precise regularity needed by the finite-hole polynomial numerator theorem;
no several-variable differentiability-to-power-series theorem is assumed. -/
theorem coefficient [DecidableEq I] (T : Finset I) (g a : I → E → ℂ) (x : E)
    (hg : ∀ i ∈ T, DifferentiableAt ℂ (g i) x)
    (ha : ∀ i ∈ T, DifferentiableAt ℂ (a i) x)
    (hi : Set.InjOn (fun i => g i x) T) (n : ℕ) :
    DifferentiableAt ℂ (fun w => (Lagrange.interpolate T (fun i => g i w)
      (fun i => a i w)).coeff n) x := by
  simp_rw [Lagrange.interpolate_eq_sum,Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul]
  apply finite_sum
  intro i hit
  have hden : (∏ j ∈ T.erase i, (g i x-g j x)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1
      (hi (Finset.mem_erase.mp hj).2 hit h.symm))
  have hd := finite_product (T.erase i) (fun j w => g i w-g j w) x
    (fun j hj => (hg i hit).sub (hg j (Finset.mem_erase.mp hj).2))
  apply ((ha i hit).div hd hden).mul
  apply product_coefficient
  intro j hj k
  by_cases hk : k=0
  · subst k
    simpa using (hg j (Finset.mem_erase.mp hj).2).neg
  · simpa only [Polynomial.coeff_sub,Polynomial.coeff_C,hk,if_false,sub_zero] using
      (differentiableAt_const ((Polynomial.X : Polynomial ℂ).coeff k))
end DifferentiableFiniteInterpolation318
