module
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Defs
public section
noncomputable section
namespace AnalyticFiniteRootProduct318
open Polynomial
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Coefficients of a finite polynomial product are finite sums of
products of coefficients. This avoids putting an auxiliary norm on the
polynomial ring or assuming analytic dependence of a selected factor. -/
lemma analytic_coeff_product (s : Finset I) (P : I → E → Polynomial ℂ) (x : E)
    (ha : ∀ i ∈ s, ∀ n, AnalyticAt ℂ (fun w => (P i w).coeff n) x)
    (n : ℕ) : AnalyticAt ℂ (fun w => (∏ i ∈ s, P i w).coeff n) x := by
  classical
  revert ha n
  induction s using Finset.induction_on with
  | empty =>
      intro ha n
      simpa only [Finset.prod_empty] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : E => (1 : Polynomial ℂ).coeff n) x)
  | @insert i s hi ih =>
      intro ha n
      simp only [Finset.prod_insert hi]
      simp_rw [Polynomial.coeff_mul]
      apply Finset.analyticAt_fun_sum
      intro k hk
      exact (ha i (Finset.mem_insert_self _ _) k.1).mul
        (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)) k.2)

@[expose] def factor (T : Finset I) (g : I → E → ℂ) (w : E) : Polynomial ℂ :=
  ∏ i ∈ T, (Polynomial.X - Polynomial.C (g i w))

lemma factor_monic (T : Finset I) (g : I → E → ℂ) (w : E) :
    (factor T g w).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)

lemma factor_degree (T : Finset I) (g : I → E → ℂ) (w : E) :
    (factor T g w).natDegree = T.card := by
  unfold factor
  rw [Polynomial.natDegree_prod_of_monic (fun _ _ => Polynomial.monic_X_sub_C _)]
  simp

lemma factor_root (T : Finset I) (g : I → E → ℂ) (w : E) (z : ℂ) :
    (factor T g w).eval z = 0 ↔ ∃ i ∈ T, g i w = z := by
  classical
  simp only [factor,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,
    Polynomial.eval_C,Finset.prod_eq_zero_iff,sub_eq_zero,eq_comm]

/-- Every coefficient of the actual finite root product is analytic
where its individual roots are analytic, including the empty product. -/
lemma factor_coeff_analytic (T : Finset I) (g : I → E → ℂ) (w : E)
    (hg : ∀ i ∈ T, AnalyticAt ℂ (g i) w) (n : ℕ) :
    AnalyticAt ℂ (fun v => (factor T g v).coeff n) w := by
  apply analytic_coeff_product
  intro i hi k
  by_cases hk : k = 0
  · subst k
    simpa using (hg i hi).neg
  · simpa only [Polynomial.coeff_sub,Polynomial.coeff_C,hk,if_false,sub_zero] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : E => (Polynomial.X : Polynomial ℂ).coeff k) w)
end AnalyticFiniteRootProduct318
