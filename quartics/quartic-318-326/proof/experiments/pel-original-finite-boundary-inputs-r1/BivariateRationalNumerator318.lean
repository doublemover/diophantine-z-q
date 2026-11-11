module
public import BivariatePrincipalOpenPolynomial318
public import ComplexPolynomialOpenPoints318
public section
noncomputable section
namespace BivariateRationalNumerator318
open Set

/-- A globally defined coefficient analytic on the TRUE two-dimensional
principal open, with a genuine uniform pole-and-growth estimate, has an
actual polynomial numerator with the SAME power of the SAME denominator.
No rationality or extension across the missing divisor is a premise. -/
theorem exists_numerator (d : MvPolynomial (Fin 2) ℂ) (hd : d ≠ 0)
    (f : (Fin 2 → ℂ) → ℂ) (M N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ v, MvPolynomial.eval v d ≠ 0 → AnalyticAt ℂ f v)
    (hb : ∀ v, MvPolynomial.eval v d ≠ 0 →
      ‖MvPolynomial.eval v d ^ M * f v‖ ≤ C * (1+‖v‖)^N) :
    ∃ P : MvPolynomial (Fin 2) ℂ, ∀ v, MvPolynomial.eval v d ≠ 0 →
      MvPolynomial.eval v P = MvPolynomial.eval v d ^ M * f v := by
  let F : ℂ × ℂ → ℂ := fun z =>
    MvPolynomial.eval ![z.1,z.2] d ^ M * f ![z.1,z.2]
  have hmap : Differentiable ℂ (fun z : ℂ × ℂ => ![z.1,z.2]) := by fun_prop
  have hF (x y : ℂ) (hxy : MvPolynomial.eval ![x,y] d ≠ 0) : DifferentiableAt ℂ F (x,y) := by
    have hpoly := (AnalyticOnNhd.eval_mvPolynomial d) ![x,y] (mem_univ _)
    exact ((hpoly.pow M).mul (hf ![x,y] hxy)).differentiableAt.comp (x,y) hmap.differentiableAt
  have hB (x y : ℂ) (hxy : MvPolynomial.eval ![x,y] d ≠ 0) :
      ‖F (x,y)‖ ≤ C*(1+‖x‖)^N*(1+‖y‖)^N := by
    have hn : ‖![x,y]‖ ≤ ‖x‖+‖y‖ := by
      apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y))).mpr
      intro i
      fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one] <;>
        linarith [norm_nonneg x,norm_nonneg y]
    have hn' : 1+‖![x,y]‖ ≤ (1+‖x‖)*(1+‖y‖) := by
      nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]
    calc
      ‖F (x,y)‖ ≤ C*(1+‖![x,y]‖)^N := hb ![x,y] hxy
      _ ≤ C*((1+‖x‖)*(1+‖y‖))^N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn' N) hC
      _ = C*(1+‖x‖)^N*(1+‖y‖)^N := by rw [mul_pow]; ring
  obtain ⟨P,hP⟩ := BivariatePrincipalOpenPolynomial318.exists_polynomial d hd F N C hC hF hB
  refine ⟨P,?_⟩
  intro v hv
  have he : ![v 0,v 1] = v := by funext i; fin_cases i <;> rfl
  simpa only [F,he] using hP (v 0) (v 1) (by simpa only [he] using hv)

/-- The same numerator gives a literal rational formula on ALL of D(d),
including every selected and unselected candidate base point there. -/
theorem exists_rational_formula (d : MvPolynomial (Fin 2) ℂ) (hd : d ≠ 0)
    (f : (Fin 2 → ℂ) → ℂ) (M N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ v, MvPolynomial.eval v d ≠ 0 → AnalyticAt ℂ f v)
    (hb : ∀ v, MvPolynomial.eval v d ≠ 0 →
      ‖MvPolynomial.eval v d ^ M * f v‖ ≤ C * (1+‖v‖)^N) :
    ∃ P : MvPolynomial (Fin 2) ℂ, ∀ v, MvPolynomial.eval v d ≠ 0 →
      f v = MvPolynomial.eval v P / MvPolynomial.eval v d ^ M := by
  obtain ⟨P,hP⟩ := exists_numerator d hd f M N C hC hf hb
  refine ⟨P,fun v hv => (eq_div_iff (pow_ne_zero M hv)).mpr ?_⟩
  rw [hP v hv,mul_comm]
end BivariateRationalNumerator318
