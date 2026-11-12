module
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Order
public section
noncomputable section
namespace AnalyticSquaredDerivative318
open Filter Set
open scoped Topology
set_option maxHeartbeats 2000000

/-- A holomorphic solution of f'²=f²h cannot leave zero at finite order:
the derivative lowers the order by one whereas the right side has at
least twice the order of f. No differential-equation uniqueness axiom. -/
theorem locally_zero {f h : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hh : AnalyticAt ℂ h z) (hz : f z=0)
    (he : ∀ᶠ w in 𝓝 z,(deriv f w)^2=(f w)^2*h w) :
    ∀ᶠ w in 𝓝 z,f w=0 := by
  apply analyticOrderAt_eq_top.mp
  have hd := hf.analyticOrderAt_deriv_add_one
  simp only [hz,sub_zero] at hd
  have he' : (deriv f)*(deriv f) =ᶠ[𝓝 z] (f*f)*h := by
    filter_upwards [he] with w hw
    simpa only [Pi.mul_apply,pow_two] using hw
  have ho := analyticOrderAt_congr he'
  rw [analyticOrderAt_mul hf.deriv hf.deriv,
    analyticOrderAt_mul (hf.mul hf) hh,analyticOrderAt_mul hf hf] at ho
  cases hn : analyticOrderAt (deriv f) z with
  | top => simpa only [hn,top_add] using hd.symm
  | coe n =>
    have hl : analyticOrderAt f z+analyticOrderAt f z ≤
        analyticOrderAt (deriv f) z+analyticOrderAt (deriv f) z := by
      rw [ho]
      exact le_add_of_nonneg_right (zero_le _)
    rw [←hd,hn] at hl
    norm_cast at hl
    omega

/-- Propagate a genuine locally constant meromorphic germ to every
regular point of the same complex plane, retaining the original function. -/
theorem meromorphic_value {f : ℂ → ℂ} (hf : Meromorphic f) (a : ℂ)
    {x : ℂ} (he : ∀ᶠ z in 𝓝 x,f z=a) (y : ℂ) (hy : ContinuousAt f y) : f y=a := by
  have hd : MeromorphicOn (fun z => f z-a) Set.univ :=
    fun z _ => (hf z).sub (analyticAt_const.meromorphicAt)
  have hx : meromorphicOrderAt (fun z => f z-a) x=⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with z hz
    simp only [hz,sub_self]
  have ht := hd.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ x) (mem_univ y) hx
  have he' : f =ᶠ[𝓝[≠] y] fun _ => a := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp ht] with z hz
    exact sub_eq_zero.mp hz
  exact tendsto_nhds_unique
    ((hy.tendsto.mono_left nhdsWithin_le_nhds).congr' he') tendsto_const_nhds
end AnalyticSquaredDerivative318
