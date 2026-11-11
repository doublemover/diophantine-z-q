module
public import PolynomialWeightBounds318
public import LocalizedComplexCoefficientAnalytic318
public section
noncomputable section
namespace PrincipalOpenWeight318
open PolynomialWeightBounds318
variable {ι X : Type*} [Fintype ι]
abbrev Base := MvPolynomial ι ℂ
@[expose] def weight (d : Base) (v : ι → ℂ) : ℝ :=
  1+‖v‖+‖MvPolynomial.eval v d‖+‖MvPolynomial.eval v d‖⁻¹

lemma one_le (d : Base) (v : ι → ℂ) : 1 ≤ weight d v := by
  unfold weight
  have h₁ := norm_nonneg v
  have h₂ := norm_nonneg (MvPolynomial.eval v d)
  have h₃ := inv_nonneg.mpr h₂
  linarith
lemma radius_le (d : Base) (v : ι → ℂ) : 1+‖v‖ ≤ weight d v := by
  unfold weight
  have h₁ := norm_nonneg v
  have h₂ := norm_nonneg (MvPolynomial.eval v d)
  have h₃ := inv_nonneg.mpr h₂
  linarith
lemma inverse_le (d : Base) (v : ι → ℂ) : ‖MvPolynomial.eval v d‖⁻¹ ≤ weight d v := by
  unfold weight
  have h₁ := norm_nonneg v
  have h₂ := norm_nonneg (MvPolynomial.eval v d)
  have h₃ := inv_nonneg.mpr h₂
  linarith

/-- Every fixed polynomial coefficient is controlled by the same weight. -/
theorem polynomial (d p : Base) (b : X → ι → ℂ) :
    Bounded (fun x => weight d (b x)) (fun x => ‖MvPolynomial.eval (b x) p‖) := by
  obtain ⟨C,hC,N,h⟩ := MvPolynomialEvaluationGrowth318.exists_growth p
  refine ⟨C,hC,N,?_⟩
  intro x
  exact (h (b x)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (radius_le d (b x)) _) hC)

/-- The entire localization is controlled, using its actual fraction
expression and the literal inverse of the SAME denominator. -/
theorem localized (d : Base) (a : Localization.Away d) (b : X → ι → ℂ)
    (hb : ∀ x, MvPolynomial.eval (b x) d ≠ 0) :
    Bounded (fun x => weight d (b x))
      (fun x => ‖ComplexPolynomialOpenPoints318.evaluation d (b x) (hb x) a‖) := by
  obtain ⟨p,n,hp⟩ := LocalizedComplexCoefficientAnalytic318.exists_ratio d a
  have hW (x : X) : 0 ≤ weight d (b x) := (zero_le_one.trans (one_le d (b x)))
  have hi : Bounded (fun x => weight d (b x)) (fun x => ‖MvPolynomial.eval (b x) d‖⁻¹) :=
    mono PolynomialWeightBounds318.weight (fun x => inverse_le d (b x))
  have h := mul hW (polynomial d p b) (pow hW hi (fun x => by positivity) n)
    (fun x => by positivity)
  apply mono h
  intro x
  have he := hp (b x) (hb x)
  rw [LocalizedComplexCoefficientAnalytic318.value_on_open] at he
  rw [he,norm_div,norm_pow,div_eq_mul_inv,inv_pow]

/-- Clearing one denominator removes the inverse part of the weight.
The resulting function has genuine ordinary polynomial growth. -/
theorem cleared_weight (d : Base) (b : X → ι → ℂ)
    (hb : ∀ x, MvPolynomial.eval (b x) d ≠ 0) :
    Bounded (fun x => 1+‖b x‖)
      (fun x => ‖MvPolynomial.eval (b x) d‖ * weight d (b x)) := by
  let R : X → ℝ := fun x => 1+‖b x‖
  have hR (x : X) : 1 ≤ R x := by dsimp [R]; positivity
  have hp : Bounded R (fun x => ‖MvPolynomial.eval (b x) d‖) := by
    obtain ⟨C,hC,N,h⟩ := MvPolynomialEvaluationGrowth318.exists_growth d
    exact ⟨C,hC,N,fun x => h (b x)⟩
  have hprod := mul (fun x => zero_le_one.trans (hR x)) hp
    (PolynomialWeightBounds318.weight (W := R)) (fun x => zero_le_one.trans (hR x))
  have hsquare := pow (fun x => zero_le_one.trans (hR x)) hp (fun x => norm_nonneg _) 2
  have hsum := add hR (add hR hprod hsquare) (const (W := R) 1)
  apply mono hsum
  intro x
  have hd : ‖MvPolynomial.eval (b x) d‖ ≠ 0 := norm_ne_zero_iff.mpr (hb x)
  dsimp [R]
  unfold weight
  have hi := mul_inv_cancel₀ hd
  nlinarith

/-- A fixed weighted bound yields a genuine uniform denominator power
and ordinary polynomial growth. No degree constancy or compactification
is assumed. -/
theorem pole_growth (d : Base) (b : X → ι → ℂ)
    (hb : ∀ x, MvPolynomial.eval (b x) d ≠ 0) (f : X → ℝ)
    (hf : Bounded (fun x => weight d (b x)) f) :
    ∃ M N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖MvPolynomial.eval (b x) d‖^M * f x ≤ C*(1+‖b x‖)^N := by
  obtain ⟨C,hC,M,hf⟩ := hf
  obtain ⟨D,hD,N,hd⟩ := cleared_weight d b hb
  refine ⟨M,N*M,C*D^M,mul_nonneg hC (pow_nonneg hD _),?_⟩
  intro x
  calc
    ‖MvPolynomial.eval (b x) d‖^M*f x ≤
        ‖MvPolynomial.eval (b x) d‖^M*(C*weight d (b x)^M) :=
      mul_le_mul_of_nonneg_left (hf x) (pow_nonneg (norm_nonneg _) _)
    _ = C*(‖MvPolynomial.eval (b x) d‖*weight d (b x))^M := by rw [mul_pow]; ring
    _ ≤ C*(D*(1+‖b x‖)^N)^M := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (zero_le_one.trans (one_le d (b x)))) (hd x) _) hC
    _ = (C*D^M)*(1+‖b x‖)^(N*M) := by rw [mul_pow,←pow_mul]; ring
end PrincipalOpenWeight318
