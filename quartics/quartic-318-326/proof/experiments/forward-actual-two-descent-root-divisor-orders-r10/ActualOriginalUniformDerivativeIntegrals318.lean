module
public import ActualOriginalParameterSliceDerivatives318
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public section
noncomputable section
namespace ActualOriginalUniformDerivativeIntegrals318
open QuadricCRTAssembly318 ActualOriginalTwistedWeight318 ActualOriginalParameterSliceDerivatives318
open MeasureTheory Set
open scoped ContDiff
set_option maxHeartbeats 16000000

lemma actual_twisted_support_subset (κ β : ℝ) (W : Coordinates ℝ → ℝ) :
    tsupport (twistedWeight κ β W) ⊆ tsupport W := by
  have hs : Function.support (fun x => (W x : ℂ)) ⊆ Function.support W := by
    intro x hx hzero
    apply hx
    simp only [hzero,Complex.ofReal_zero]
  exact tsupport_mul_subset_left.trans (closure_mono hs)

lemma actual_twisted_derivative_zero (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (j : ℕ) (x : Coordinates ℝ) (hx : x ∉ tsupport W) :
    iteratedFDeriv ℝ j (twistedWeight κ β W) x = 0 := by
  by_contra hn
  exact hx ((support_iteratedFDeriv_subset j).trans (actual_twisted_support_subset κ β W) hn)

/-- One polynomial beta bound controls ALL source derivatives up to n
on the actual original support. The exponent and constant are independent
of beta, derivative index and source point. -/
lemma actual_uniform_derivative_support_bound (κ : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (n : ℕ) :
    ∃ (k : ℕ) (A : ℝ), 0 ≤ A ∧ ∀ j ≤ n, ∀ β : ℝ, ∀ x ∈ tsupport W,
      ‖iteratedFDeriv ℝ j (twistedWeight κ β W) x‖ ≤ A*(1+‖β‖)^k := by
  obtain ⟨k,C,hC,hbound⟩ := actual_twisted_source_derivative_bound κ W hW hWc n
  obtain ⟨R0,hR0⟩ := hWc.isCompact.bddAbove_image (continuous_norm.continuousOn :
    ContinuousOn (fun x : Coordinates ℝ => ‖x‖) (tsupport W))
  let R : ℝ := max 0 R0
  have hR : 0 ≤ R := le_max_left _ _
  refine ⟨k,C*(1+R)^k,by positivity,fun j hj β x hx => ?_⟩
  have hxR : ‖x‖ ≤ R := (hR0 ⟨x,hx,rfl⟩).trans (le_max_right _ _)
  have hmax : max ‖β‖ ‖x‖ ≤ ‖β‖+R :=
    max_le (le_add_of_nonneg_right hR) (hxR.trans (le_add_of_nonneg_left (norm_nonneg β)))
  have hb : 1+‖(β,x)‖ ≤ (1+‖β‖)*(1+R) := by
    rw [Prod.norm_def]
    nlinarith [norm_nonneg β]
  calc
    _ ≤ C*(1+‖(β,x)‖)^k := hbound j hj β x
    _ ≤ C*((1+‖β‖)*(1+R))^k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb k) hC
    _ = (C*(1+R)^k)*(1+‖β‖)^k := by rw [mul_pow]; ring

/-- Uniform polynomial beta control of the actual L1 source derivative
norms, in the original product volume. Compactness supplies finite volume;
every derivative is actually zero off the SAME original weight support. -/
theorem actual_uniform_derivative_integral_bound (κ : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (n : ℕ) :
    ∃ (k : ℕ) (A : ℝ), 0 ≤ A ∧ ∀ j ≤ n, ∀ β : ℝ,
      (∫ x : Coordinates ℝ, ‖iteratedFDeriv ℝ j (twistedWeight κ β W) x‖) ≤
        A*(1+‖β‖)^k := by
  obtain ⟨k,A,hA,hbound⟩ := actual_uniform_derivative_support_bound κ W hW hWc n
  refine ⟨k,A*volume.real (tsupport W),by positivity,fun j hj β => ?_⟩
  have hz : ∀ x : Coordinates ℝ, x ∉ tsupport W →
      ‖iteratedFDeriv ℝ j (twistedWeight κ β W) x‖=0 := by
    intro x hx
    rw [actual_twisted_derivative_zero κ β W j x hx,norm_zero]
  calc
    _ = ∫ x in tsupport W, ‖iteratedFDeriv ℝ j (twistedWeight κ β W) x‖ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm
    _ ≤ ‖∫ x in tsupport W, ‖iteratedFDeriv ℝ j (twistedWeight κ β W) x‖‖ := le_abs_self _
    _ ≤ (A*(1+‖β‖)^k)*volume.real (tsupport W) :=
      norm_setIntegral_le_of_norm_le_const hWc.isCompact.measure_lt_top
        (fun x hx => by simpa only [norm_norm] using hbound j hj β x hx)
    _ = (A*volume.real (tsupport W))*(1+‖β‖)^k := by ring

end ActualOriginalUniformDerivativeIntegrals318
