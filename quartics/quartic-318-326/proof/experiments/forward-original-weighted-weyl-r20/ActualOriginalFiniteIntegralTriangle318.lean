module
public import ActualOriginalPrefixMinorMoment318
public section
noncomputable section
namespace ActualOriginalFiniteIntegralTriangle318
open MeasureTheory
open scoped BigOperators

lemma actual_integral_norm_add (μ : Measure ℝ) (f g : ℝ → ℂ)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ t, ‖f t+g t‖ ∂μ)≤(∫ t, ‖f t‖ ∂μ)+(∫ t, ‖g t‖ ∂μ) := by
  have hh := integral_mono (hf.add hg).norm (hf.norm.add hg.norm)
    (fun t => norm_add_le (f t) (g t))
  simpa only [integral_add hf.norm hg.norm] using hh

lemma actual_integral_norm_sum {ι : Type*} (μ : Measure ℝ) (s : Finset ι)
    (f : ι → ℝ → ℂ) (hf : ∀ i∈s, Integrable (f i) μ) :
    (∫ t, ‖∑ i∈s, f i t‖ ∂μ)≤∑ i∈s, ∫ t, ‖f i t‖ ∂μ := by
  have hi := integrable_finsetSum s hf
  have hj := integrable_finsetSum s (fun i hi => (hf i hi).norm)
  have hh := integral_mono hi.norm hj (fun t => norm_sum_le s (fun i => f i t))
  simpa only [integral_finsetSum s (fun i hi => (hf i hi).norm)] using hh

end ActualOriginalFiniteIntegralTriangle318
