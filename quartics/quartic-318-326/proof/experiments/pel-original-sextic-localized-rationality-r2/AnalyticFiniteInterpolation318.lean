module
public import AnalyticFiniteRootProduct318
public import Mathlib.LinearAlgebra.Lagrange
public section
noncomputable section
namespace AnalyticFiniteInterpolation318
open Polynomial
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma analytic_product (T : Finset I) (f : I → E → ℂ) (x : E)
    (hf : ∀ i ∈ T, AnalyticAt ℂ (f i) x) :
    AnalyticAt ℂ (fun w => ∏ i ∈ T, f i w) x := by
  classical
  revert hf
  induction T using Finset.induction_on with
  | empty => intro hf; simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : E => (1 : ℂ)) x)
  | @insert i T hi ih =>
      intro hf
      simpa only [Finset.prod_insert hi] using
        (hf i (Finset.mem_insert_self _ _)).mul
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Actual finite Lagrange interpolation varies analytically coefficient
by coefficient wherever all nodes remain distinct and the supplied values
are analytic. No norm or analytic structure on the polynomial ring is used. -/
theorem coefficient_analytic [DecidableEq I] (T : Finset I)
    (g a : I → E → ℂ) (x : E)
    (hg : ∀ i ∈ T, AnalyticAt ℂ (g i) x)
    (ha : ∀ i ∈ T, AnalyticAt ℂ (a i) x)
    (hi : Set.InjOn (fun i => g i x) T) (n : ℕ) :
    AnalyticAt ℂ (fun w => (Lagrange.interpolate T (fun i => g i w)
      (fun i => a i w)).coeff n) x := by
  simp_rw [Lagrange.interpolate_eq_sum,Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul]
  apply Finset.analyticAt_fun_sum
  intro i hit
  have hden : (∏ j ∈ T.erase i, (g i x - g j x)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1
      (hi (Finset.mem_erase.mp hj).2 hit h.symm))
  have hd := analytic_product (T.erase i) (fun j w => g i w - g j w) x
    (fun j hj => (hg i hit).sub (hg j (Finset.mem_erase.mp hj).2))
  exact ((ha i hit).div hd hden).mul
    (AnalyticFiniteRootProduct318.factor_coeff_analytic (T.erase i) g x
      (fun j hj => hg j (Finset.mem_erase.mp hj).2) n)
end AnalyticFiniteInterpolation318
