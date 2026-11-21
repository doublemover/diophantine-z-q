module
public import ActualTZLiteralAbsoluteEuler318
public import ActualTZLiteralMellinTensor318
public section
noncomputable section
namespace ActualTZMellinFiniteGuard318
open MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius
open ActualTZPositiveEulerMajorant318
open ActualTZMellinKernel318 ActualTZLiteralMellinTensor318 ActualTZLiteralAbsoluteEuler318
open ActualTZLiteralSchwartz318
open ActualTZMultiLinearCRT318 (jointDensity)

variable {I : Type*} [Fintype I] [DecidableEq I]

@[expose] def s1 (L : ℝ) (ξ : Slot I→ℝ) (i : I) : ℂ :=
  mode (ξ (i,true))/(L:ℂ)
@[expose] def s2 (L : ℝ) (ξ : Slot I→ℝ) (i : I) : ℂ :=
  mode (ξ (i,false))/(L:ℂ)

/-- First slot is Bool.true and second is Bool.false, exactly as in
ActualTZMultiSieveCell318.paired. Both have regulator real part 1/L. -/
theorem real_parts (L : ℝ) (ξ : Slot I→ℝ) (i : I) :
    (s1 L ξ i).re=1/L ∧ (s2 L ξ i).re=1/L := by
  constructor <;> simp only [s1,s2,Complex.div_ofReal_re,mode_re]

theorem finite_moving_majorant (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (L : ℝ) (hL : 0<L) (ξ : Slot I→ℝ) :
    (∑ d : Choices I P,‖choiceWeight W P a b (s1 L ξ) (s2 L ξ) d‖) ≤
        ‖riemannZeta ((1+1/L:ℝ):ℂ)‖^(offCount I) := by
  apply assignment_zeta W P a b hU (1/L) (by positivity)
  · intro i
    rw [(real_parts L ξ i).1]
  · intro i
    rw [(real_parts L ξ i).2]

theorem polynomial_guard (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (L : ℝ) (hL : 0<L) (ξ : Slot I→ℝ) :
    (∑ d : Choices I P,‖choiceWeight W P a b (s1 L ξ) (s2 L ξ) d‖) ≤
      (1+L)^(offCount I) := by
  refine (finite_moving_majorant W P a b hU L hL ξ).trans
    (pow_le_pow_left₀ (norm_nonneg _) ?_ _)
  simpa only [one_div,inv_inv] using zeta_norm_upper (1/L) (by positivity)

/-- Use the same signed CRT density and original two Möbius slots as
the ordinary integer-interval finite main. -/
def crc (W : ℕ) (a : I→ℤ) (b : I→ℕ) (d : Digits I) : ℂ :=
  (jointDensity W d (a ∘ Prod.fst) (b ∘ Prod.fst):ℂ)*
    ∏ j : Slot I,((ArithmeticFunction.moebius (d j):ℤ):ℂ)

/-- A finite positive divisor table with the actual signed
CRT coefficient and the literal original φ(W)/W log-R normalization.
This does not replace d by an Euler assignment until the separate
prime-support reindex / mass identity has been applied. -/
theorem physical_divisor_fubini (C : Cutoff) (R : ℝ) (hR : 1<R)
    (W : ℕ) (a : I→ℤ) (b : I→ℕ)
    (Q : Finset (Digits I)) (hQ : ∀ d∈Q,∀ j,0<d j) :
    let A : ℂ := ((((Nat.totient W:ℝ)/(W:ℝ))*Real.log R:ℝ):ℂ)^Fintype.card I
    A*(∫ ξ, (∑ d∈Q,crc W a b d*rowProduct C (Real.log R) d ξ)
      ∂ActualTZLiteralMellinTensor318.μ I) =
    A*∑ d∈Q.filter (fun d => ∀ j,d j≤⌊R⌋₊),crc W a b d*
      (∏ j : Slot I,(C.χ (Real.log (d j:ℝ)/Real.log R):ℂ)) := by
  intro A
  rw [restore_literal_cut C R hR Q (crc W a b) hQ]

/-- Nonnegative frequency envelope on the actual two slots. Uniform
in W,P,intercepts and all angular frequencies, with no conditioning
on the other sample variables. -/
theorem absolute_frequency_guard (C : Cutoff) (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (L : ℝ) (hL : 0<L) (ξ : Slot I→ℝ) :
    (∑ d : Choices I P,‖(∏ j : Slot I,φ C (ξ j))*
      choiceWeight W P a b (s1 L ξ) (s2 L ξ) d‖) ≤
      (∏ j : Slot I,‖φ C (ξ j)‖)*(1+L)^(offCount I) := by
  simp only [norm_mul,Complex.norm_prod,←Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left (polynomial_guard W P a b hU L hL ξ)
  exact Finset.prod_nonneg fun _ _ => norm_nonneg _

theorem envelope_integrable (C : Cutoff) (L : ℝ) :
    Integrable (fun ξ : Slot I→ℝ => (∏ j : Slot I,‖φ C (ξ j)‖)*(1+L)^(offCount I))
      (ActualTZLiteralMellinTensor318.μ I) := by
  exact (Integrable.fintype_prod (fun _ : Slot I => (φ_integrable C).norm)).mul_const _

end ActualTZMellinFiniteGuard318
