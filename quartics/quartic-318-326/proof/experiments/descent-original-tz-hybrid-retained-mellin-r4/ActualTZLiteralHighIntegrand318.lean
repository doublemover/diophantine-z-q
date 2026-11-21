module
public import ActualTZAngularTensorTail318
public import ActualTZHighBandPower318
public import ActualTZFiniteChoiceIntegrand318
public section
noncomputable section
namespace ActualTZLiteralHighIntegrand318
open MeasureTheory
open scoped BigOperators
open ActualTZAngularTensorTail318 ActualTZHighBandPower318 ActualTZLowFrequencyPole318
open ActualTZLiteralSchwartz318 ActualTZMellinFiniteGuard318 ActualTZLiteralMellinTensor318
open ActualTZLiteralAbsoluteEuler318 ActualTZFiniteChoiceIntegrand318

variable {I : Type*} [Fintype I] [DecidableEq I]

@[expose] def normalizer (W : ℕ) (L : ℝ) : ℂ :=
  (((Nat.totient W:ℂ)/(W:ℂ))*(L:ℂ))^Fintype.card I

def integrand (C : Cutoff) (W P : ℕ) (a : I→ℤ) (b : I→ℕ) (L : ℝ) (ξ : Slot I→ℝ) : ℂ :=
  normalizer (I:=I) W L*(∏ j : Slot I,φ C (ξ j))*
    (∏ p : PrimeAt P,∑ d : Pair I,entry W P a b (s1 L ξ) (s2 L ξ) p d)

theorem literal_integrable (C : Cutoff) (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (L : ℝ) :
    Integrable (integrand C W P a b L) (μ I) := by
  have H (ξ : Slot I→ℝ) :
      integrand C W P a b L ξ = normalizer (I:=I) W L*
        (∑ d∈digitTable I P,crc W a b d*rowProduct C L d ξ) := by
    rw [integrand,signed_prime_product,mul_assoc,choice_integrand C W P a b hU]
  have hEq : integrand C W P a b L = fun ξ : Slot I→ℝ=>normalizer (I:=I) W L*
      (∑ d∈digitTable I P,crc W a b d*rowProduct C L d ξ) := funext H
  rw [hEq]
  exact (integrable_finsetSum _ (fun d hd =>
    (rowProduct_integrable C L d (table_pos P d hd)).const_mul (crc W a b d))).const_mul _

private theorem norm_normalizer (W : ℕ) (hW : 0<W) (L : ℝ) (hL : 0≤L) :
    ‖normalizer (I:=I) W L‖≤L^Fintype.card I := by
  have hWR : 0<(W:ℝ) := by exact_mod_cast hW
  have hA : (Nat.totient W:ℝ)/(W:ℝ)≤1 :=
    (div_le_one hWR).2 (by exact_mod_cast Nat.totient_le W)
  have hP : 0≤(Nat.totient W:ℝ)/(W:ℝ) := by positivity
  simp only [normalizer,norm_pow,norm_mul,norm_div,Complex.norm_natCast,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL]
  exact pow_le_pow_left₀ (mul_nonneg hP hL)
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hL) _

theorem literal_domination (C : Cutoff) (W P : ℕ) (hW : 0<W) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (L : ℝ) (hL : 0<L) (ξ : Slot I→ℝ) :
    ‖integrand C W P a b L ξ‖≤
      (L^Fintype.card I*(1+L)^(offCount I))*density C ξ := by
  rw [integrand,signed_prime_product]
  simp only [norm_mul,Complex.norm_prod,←density]
  have hSum : ‖∑ d : Choices I P,choiceWeight W P a b (s1 L ξ) (s2 L ξ) d‖≤
      (1+L)^(offCount I) :=
    (norm_sum_le _ _).trans (polynomial_guard W P a b hU L hL ξ)
  calc
    _ ≤ ((L^Fintype.card I)*density C ξ)*(1+L)^(offCount I) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right (norm_normalizer (I:=I) W hW L hL.le) (density_nonneg C ξ))
        hSum (norm_nonneg _) (mul_nonneg (by positivity) (density_nonneg C ξ))
    _ = _ := by ring

/-- The actual signed ordinary finite-main angular tail is O(L^-2)
with an explicit Schwartz moment constant independent of all wrap
intercepts, wheel, P, and the outer sample. -/
theorem high_error (C : Cutoff) (W P : ℕ) (hW : 0<W) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (L : ℝ) (hL : 1≤L) :
    let d := 4*(Fintype.card I+offCount I+2)
    ‖∫ ξ in (fullBand I (band L))ᶜ,integrand C W P a b L ξ ∂μ I‖ ≤
      ((2:ℝ)^(offCount I)/L^2)*(∫ ξ,moments C d ξ ∂μ I) := by
  intro d
  have hp : 0<L := zero_lt_one.trans_le hL
  have hd : 0<band L := Real.rpow_pos_of_pos hp _
  have H := use_outside_bound C d (band L) hd (integrand C W P a b L)
    (literal_integrable C W P a b hU L) (L^Fintype.card I*(1+L)^(offCount I)) (by positivity)
    (literal_domination C W P hW a b hU L hp)
  refine H.trans ?_
  calc
    _ = (L^Fintype.card I*(1+L)^(offCount I)*(band L^d)⁻¹)*
        (∫ ξ,moments C d ξ ∂μ I) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (high_power L hL (Fintype.card I) (offCount I))
      (integral_nonneg (moments_nonneg C d))

end ActualTZLiteralHighIntegrand318
