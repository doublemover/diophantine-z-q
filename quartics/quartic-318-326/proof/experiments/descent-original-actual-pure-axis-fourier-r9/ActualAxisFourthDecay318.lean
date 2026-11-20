module
public import ActualPureChartKernel318
import all ActualPureChartKernel318
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public section
noncomputable section
namespace ActualAxisFourthDecay318
open MeasureTheory
open scoped FourierTransform ContDiff SchwartzMap
open AffineThreePoissonRows318 ActualPureChartKernel318

/-- One-use quartic Fourier estimate: no mixed derivatives. -/
theorem quartic_row_bound {f : ℝ→ℂ} (hf : ContDiff ℝ 4 f)
    (hfi : ∀ n≤(4:ℕ),Integrable (iteratedDeriv n f)) (ξ C : ℝ)
    (hC : (∫ z,‖f z‖)+((2*Real.pi)^4)⁻¹*(∫ z,‖iteratedDeriv 4 f z‖)≤C) :
    ‖𝓕 f ξ‖≤C/(1+|ξ|^4) := by
  apply (le_div_iff₀ (by positivity : 0<1+|ξ|^4)).mpr
  rw [mul_comm]
  exact (Real.one_add_pow_mul_norm_fourier_le hf hfi ξ).trans hC

private theorem phase_norm (a : ℝ) : ‖phase a‖=1 := Circle.norm_coe _

private theorem phase_continuous : Continuous phase :=
  continuous_subtype_val.comp Real.continuous_fourierChar

def tilt (κ τ X : ℝ) (i : Fin 4) (ξ η ζ : ℝ) (p : FreePoint) : ℂ :=
  phase (-(p.1*ζ+p.2.1*η+p.2.2*ξ))*kernel κ τ X i p

/-- All frequencies on the SAME chart have an integrable kernel. Unit
phases do not alter the exact compact support or the L¹ mass. -/
theorem tilt_integrable (κ τ X : ℝ) (i : Fin 4) (hτ : 0<τ) (ξ η ζ : ℝ) :
    Integrable (tilt κ τ X i ξ η ζ) measure3 := by
  have hp : Continuous (fun p : FreePoint => phase (-(p.1*ζ+p.2.1*η+p.2.2*ξ))) :=
    phase_continuous.comp (by fun_prop)
  have h := actualKernel_integrable κ τ X i hτ
  exact h.bdd_mul hp.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => (phase_norm _).le))

/-- Exact actual full Fourier kernel, for all signed real frequencies,
without any sampled row or all-order Jet assumption. -/
theorem actual_F₃_tilt (κ τ X : ℝ) (i : Fin 4) (hτ : 0<τ) (ξ η ζ : ℝ) :
    F₃ (W κ τ i X) ξ η ζ = ∫ p, tilt κ τ X i ξ η ζ p ∂measure3 := by
  have hi := tilt_integrable κ τ X i hτ ξ η ζ
  change Integrable (tilt κ τ X i ξ η ζ)
    ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) at hi
  unfold measure3
  rw [integral_prod _ hi]
  simp only [F₃,F₂,F₁,Real.fourier_real_eq,Circle.smul_def,smul_eq_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with v hv
  rw [integral_prod _ hv]
  apply integral_congr_ae
  filter_upwards [] with t
  apply integral_congr_ae
  filter_upwards [] with z
  change phase (-(v*ζ))*(phase (-(t*η))*(phase (-(z*ξ))*W κ τ i X z t v)) =
    phase (-(v*ζ+t*η+z*ξ))*W κ τ i X z t v
  rw [show -(v*ζ+t*η+z*ξ)=-(v*ζ)+(-(t*η)+-(z*ξ)) by ring,phase_add,phase_add]
  ring

/-- A quartic row envelope integrated over the other two variables.
Once product ordering is the physical axis order, this needs no hybrid
summability nor any higher mixed derivative. -/
theorem integrated_axis_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] (G : α×ℝ→ℂ)
    (hG : Integrable G (μ.prod volume)) (K : Set α) (hK : MeasurableSet K)
    (hfin : μ K≠⊤) (C ξ : ℝ)
    (hz : ∀ a∉K, (∫ z, G (a,z))=0)
    (hb : ∀ a∈K, ‖∫ z, G (a,z)‖≤C/(1+|ξ|^4)) :
    ‖∫ p,G p ∂(μ.prod volume)‖≤μ.real K*(C/(1+|ξ|^4)) := by
  have hi := hG.integral_prod_left
  rw [integral_prod _ hG]
  calc
    _ ≤ ∫ a,‖∫ z,G (a,z)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ a in K,‖∫ z,G (a,z)‖ ∂μ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro a ha
      rw [hz a ha,norm_zero]
    _ ≤ ∫ _a in K,C/(1+|ξ|^4) ∂μ :=
      setIntegral_mono_on hi.norm.integrableOn (integrableOn_const hfin) hK hb
    _ = _ := by rw [setIntegral_const,smul_eq_mul]

/-- Final scalar reduction to the max-norm shell envelope; no
mixed fourth/sixth derivative is required by the nonzero tail. -/
theorem quartic_to_shell (C t : ℝ) (hC : 0≤C) (ht : 0≤t) :
    C/(1+t^4)≤8*C/(1+t)^4 := by
  have h₁ : 0≤(t-1)^2 := sq_nonneg _
  have h₂ : 0≤(t^2-1)^2 := sq_nonneg _
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have he : (1+t)^4≤8*(1+t^4) := by
    have hA : (1+t)^2≤2*(1+t^2) := by nlinarith only [h₁]
    have hB : (1+t^2)^2≤2*(1+t^4) := by nlinarith only [h₂]
    have hSq := (sq_le_sq₀ (show 0≤(1+t)^2 by positivity)
      (show 0≤2*(1+t^2) by positivity)).mpr hA
    nlinarith only [hSq,hB]
  convert mul_le_mul_of_nonneg_left he hC using 1 <;> ring

end ActualAxisFourthDecay318
