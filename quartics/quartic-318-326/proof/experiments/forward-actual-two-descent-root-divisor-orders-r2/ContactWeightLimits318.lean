module
public import ContactWeightWitness318
public import Mathlib.Analysis.Polynomial.Basic
public section
noncomputable section
namespace ContactWeightLimits318
open Filter Polynomial ContactWeightWitness318
open scoped Topology

@[expose] def contactPolynomial : ℚ[X] :=
  X*(X+C (1/2))*(X+C 1)*(X-C (1/2399))*(X+C (32/407))

lemma contactPolynomial_eval (t : ℚ) : contactPolynomial.eval t=contact t := by
  simp [contactPolynomial,contact]

lemma contactPolynomial_degree : contactPolynomial.degree=5 := by
  simp only [contactPolynomial,Polynomial.degree_mul,Polynomial.degree_X,
    Polynomial.degree_X_add_C,Polynomial.degree_X_sub_C]
  norm_num

lemma weight_limit : Tendsto weight atTop (𝓝 0) := by
  change Tendsto (fun t : ℚ => (t-1)^2/contact t) atTop (𝓝 0)
  have he := Polynomial.div_tendsto_atTop_zero_of_degree_lt
    ((X-C (1:ℚ))^2) contactPolynomial (by
      simp only [Polynomial.degree_pow,Polynomial.degree_X_sub_C,contactPolynomial_degree]
      norm_num)
  simpa only [Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,
    Polynomial.eval_C,contactPolynomial_eval] using he

lemma weight7_formula (t : ℚ) : (weight t)^7*(t-1)^18=(t-1)^32/(contact t)^7 := by
  simp only [weight,div_pow,div_mul_eq_mul_div]
  congr 1
  ring

lemma weight13_formula (t : ℚ) : (weight t)^13*(t-1)^36=(t-1)^62/(contact t)^13 := by
  simp only [weight,div_pow,div_mul_eq_mul_div]
  congr 1
  ring

lemma weight25_formula (t : ℚ) : (weight t)^25*(t-1)^72=(t-1)^122/(contact t)^25 := by
  simp only [weight,div_pow,div_mul_eq_mul_div]
  congr 1
  ring

/-- The exact original x-weight tends to zero. Its numerator degree is32,
denominator degree35; this is the genuine cubic decay, not a supplied bound. -/
theorem weight7_limit : Tendsto (fun t : ℚ => (weight t)^7*(t-1)^18) atTop (𝓝 0) := by
  simp_rw [weight7_formula]
  have he := Polynomial.div_tendsto_atTop_zero_of_degree_lt
    ((X-C (1:ℚ))^32) (contactPolynomial^7) (by
      simp only [Polynomial.degree_pow,Polynomial.degree_X_sub_C,contactPolynomial_degree]
      norm_num)
  simpa only [Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,
    Polynomial.eval_C,contactPolynomial_eval] using he

theorem weight13_limit : Tendsto (fun t : ℚ => (weight t)^13*(t-1)^36) atTop (𝓝 0) := by
  simp_rw [weight13_formula]
  have he := Polynomial.div_tendsto_atTop_zero_of_degree_lt
    ((X-C (1:ℚ))^62) (contactPolynomial^13) (by
      simp only [Polynomial.degree_pow,Polynomial.degree_X_sub_C,contactPolynomial_degree]
      norm_num)
  simpa only [Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,
    Polynomial.eval_C,contactPolynomial_eval] using he

theorem weight25_limit : Tendsto (fun t : ℚ => (weight t)^25*(t-1)^72) atTop (𝓝 0) := by
  simp_rw [weight25_formula]
  have he := Polynomial.div_tendsto_atTop_zero_of_degree_lt
    ((X-C (1:ℚ))^122) (contactPolynomial^25) (by
      simp only [Polynomial.degree_pow,Polynomial.degree_X_sub_C,contactPolynomial_degree]
      norm_num)
  simpa only [Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,
    Polynomial.eval_C,contactPolynomial_eval] using he

/-- The reciprocal of the actual e*delta weight also decays, now linearly. -/
theorem inverse_ed_limit : Tendsto (fun t : ℚ => contact t/(t-1)^6) atTop (𝓝 0) := by
  have he := Polynomial.div_tendsto_atTop_zero_of_degree_lt contactPolynomial
    ((X-C (1:ℚ))^6) (by
      simp only [Polynomial.degree_pow,Polynomial.degree_X_sub_C,contactPolynomial_degree]
      norm_num)
  simpa only [Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,
    Polynomial.eval_C,contactPolynomial_eval] using he

end ContactWeightLimits318
