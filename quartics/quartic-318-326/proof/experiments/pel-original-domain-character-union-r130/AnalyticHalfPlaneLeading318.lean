module
public import UpperHalfPlanePowerRays318
public import Mathlib.Analysis.Analytic.Order
public section
noncomputable section
namespace AnalyticHalfPlaneLeading318
open Complex Set Filter
open scoped Topology
set_option maxHeartbeats 2200000

lemma ray_tendsto (η : ℂ) :
    Tendsto (fun t : ℝ => (t:ℂ)*η) (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
  have hc : ContinuousAt (fun t : ℝ => (t:ℂ)*η) 0 := by fun_prop
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- An actual sign on a positive ray constrains the leading analytic
coefficient. The positive real radial factor is cancelled before taking
the limit; no sector coverage or derivative assumption is supplied. -/
theorem leading_nonneg (f g : ℂ → ℂ) (n : ℕ) (η : ℂ)
    (hg : ContinuousAt g 0)
    (he : ∀ᶠ z in 𝓝 (0:ℂ),f z=z^n*g z)
    (hs : ∀ᶠ t in 𝓝[>] (0:ℝ),0≤(f ((t:ℂ)*η)).im) :
    0≤(η^n*g 0).im := by
  have ht := ray_tendsto η
  have hl : Tendsto (fun t : ℝ => (η^n*g ((t:ℂ)*η)).im)
      (𝓝[>] (0:ℝ)) (𝓝 ((η^n*g 0).im)) :=
    Complex.continuous_im.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul (hg.tendsto.comp ht))
  apply ge_of_tendsto hl
  filter_upwards [ht.eventually he,hs,self_mem_nhdsWithin] with t ht' hs' htpos
  have hpow : (0:ℝ)<t^n := pow_pos htpos _
  have hi : (f ((t:ℂ)*η)).im=t^n*(η^n*g ((t:ℂ)*η)).im := by
    rw [ht',mul_pow,mul_assoc,←Complex.ofReal_pow]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  rw [hi] at hs'
  exact nonneg_of_mul_nonneg_left hs' hpow

/-- Actual real-axis boundary values force the nonzero leading
coefficient itself to be real. -/
theorem leading_real (f g : ℂ → ℂ) (n : ℕ) (hg : ContinuousAt g 0)
    (he : ∀ᶠ z in 𝓝 (0:ℂ),f z=z^n*g z)
    (hr : ∀ᶠ z in 𝓝 (0:ℂ),z.im=0 → (f z).im=0) : (g 0).im=0 := by
  have hpos : ∀ᶠ t in 𝓝[>] (0:ℝ),0≤(f ((t:ℂ)*1)).im := by
    filter_upwards [(ray_tendsto 1).eventually hr] with t ht
    rw [ht (by simp)]
  have hneg : ∀ᶠ t in 𝓝[>] (0:ℝ),0≤(-f ((t:ℂ)*1)).im := by
    filter_upwards [(ray_tendsto 1).eventually hr] with t ht
    rw [Complex.neg_im,ht (by simp),neg_zero]
  have he' : ∀ᶠ z in 𝓝 (0:ℂ),(-f z)=z^n*(-g z) := by
    filter_upwards [he] with z hz
    rw [hz,mul_neg]
  have hp := leading_nonneg f g n 1 hg he hpos
  have hn := leading_nonneg (fun z => -f z) (fun z => -g z) n 1 hg.neg he' hneg
  simp only [one_pow,one_mul,Complex.neg_im] at hp hn
  linarith

/-- Each genuine upper ray inherits the actual upper-half-plane sign. -/
theorem upper_ray_leading (f g : ℂ → ℂ) (n : ℕ) (η : ℂ)
    (hg : ContinuousAt g 0) (hη : 0<η.im)
    (he : ∀ᶠ z in 𝓝 (0:ℂ),f z=z^n*g z)
    (hu : ∀ᶠ z in 𝓝 (0:ℂ),0<z.im → 0<(f z).im) :
    0≤(η^n*g 0).im := by
  apply leading_nonneg f g n η hg he
  filter_upwards [(ray_tendsto η).eventually hu,self_mem_nhdsWithin] with t ht htp
  apply (ht ?_).le
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using mul_pos htp hη
end AnalyticHalfPlaneLeading318
