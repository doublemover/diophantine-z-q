module
public import LocalMultiplicativeGerm318
public section
noncomputable section
namespace LocalAdditiveGerm318
open Set Filter Metric Topology
/-- A genuine local additive law yields a local affine function by
actual differentiation. No measurable-additive or logarithm premise. -/
theorem affine_germ(R:ℂ→ℂ)(r:ℝ)(hr:0<r)
    (hd:∀t:ℂ,‖t‖<r→DifferentiableAt ℂ R t)
    (ha:∀a b:ℂ,‖a‖<r→‖b‖<r→‖a+b‖<r→R (a+b)+R 0=R a+R b):
    ∀ᶠt in 𝓝 (0:ℂ),R t=R 0+deriv R 0*t:=by
  have hd0:DifferentiableAt ℂ R 0:=hd 0 (by simpa using hr)
  have he:∀t:ℂ,‖t‖<r/2→deriv R t=deriv R 0:=by
    intro t ht
    have htr:‖t‖<r:=by linarith
    have hne:∀ᶠb in 𝓝 (0:ℂ),‖b‖<r∧‖t+b‖<r:=by
      have hb:∀ᶠb in 𝓝 (0:ℂ),‖b‖<r:=
        continuous_norm.continuousAt (isOpen_Iio.mem_nhds (by simpa using hr))
      have ht':∀ᶠb in 𝓝 (0:ℂ),‖t+b‖<r:=
        (continuous_const.add continuous_id).norm.continuousAt
          (isOpen_Iio.mem_nhds (by simpa only [add_zero] using htr))
      exact hb.and ht'
    have hident:(fun b:ℂ=>R (t+b)+R 0)=ᶠ[𝓝 (0:ℂ)] (fun b=>R t+R b):=by
      filter_upwards [hne] with b hb
      exact ha t b htr hb.1 hb.2
    have hl:HasDerivAt (fun b:ℂ=>R (t+b)+R 0) (deriv R t) 0:=by
      simpa only [add_zero,mul_one] using
        (((hd t htr).hasDerivAt.comp 0 ((hasDerivAt_id (0:ℂ)).const_add t)).add_const (R 0))
    have hh:HasDerivAt (fun b:ℂ=>R t+R b) (deriv R 0) 0:=hd0.hasDerivAt.const_add (R t)
    exact (hl.congr_of_eventuallyEq hident.symm).unique hh
  let W:ℂ→ℂ:=fun t=>R t-deriv R 0*t
  have hw:∀t∈ball (0:ℂ) (r/2),HasDerivAt W 0 t:=by
    intro t ht
    have htn:‖t‖<r/2:=by simpa only [mem_ball,dist_zero_right] using ht
    have h:=((hd t (by linarith)).hasDerivAt).sub
      ((hasDerivAt_id t).const_mul (deriv R 0))
    simpa only [he t htn,mul_one,sub_self] using h
  have hc:∀t∈ball (0:ℂ) (r/2),W t=W 0:=by
    intro t ht
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0:ℂ) (r/2)).isPreconnected
      (fun z hz=>(hw z hz).differentiableAt.differentiableWithinAt) (fun z hz=>(hw z hz).deriv)
      ht (mem_ball_self (by linarith))
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (show 0<r/2 by linarith))] with t ht
  have h:=hc t ht
  dsimp only [W] at h
  simpa only [mul_zero,sub_zero,sub_eq_iff_eq_add,add_comm] using h
end LocalAdditiveGerm318
