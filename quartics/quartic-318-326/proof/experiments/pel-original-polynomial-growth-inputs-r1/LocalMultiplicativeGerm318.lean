module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.CauchyIntegral
public section
noncomputable section
namespace LocalMultiplicativeGerm318
open Set Filter Metric Topology

/-- A genuine local multiplicative law forces an exponential germ.
The proof differentiates the original law and solves a local scalar ODE;
no logarithm branch or globally zero-free quotient is assumed. -/
theorem exponential_germ(R:ℂ→ℂ)(r:ℝ)(hr:0<r)(h0:R 0≠0)
    (hd:∀t:ℂ,‖t‖<r→DifferentiableAt ℂ R t)
    (hm:∀a b:ℂ,‖a‖<r→‖b‖<r→‖a+b‖<r→R (a+b)*R 0=R a*R b):
    ∀ᶠt in 𝓝 (0:ℂ),R t=R 0*Complex.exp ((deriv R 0/R 0)*t):=by
  let l:ℂ:=deriv R 0/R 0
  have hzero:‖(0:ℂ)‖<r:=by simpa using hr
  have heq:∀a:ℂ,‖a‖<r/2→deriv R a=l*R a:=by
    intro a ha
    have har:‖a‖<r:=lt_trans ha (by linarith)
    have hs:∀ᶠb in 𝓝 (0:ℂ),R (a+b)*R 0=R a*R b:=by
      have hb:∀ᶠb in 𝓝 (0:ℂ),‖b‖<r:=
        continuous_norm.continuousAt (isOpen_Iio.mem_nhds hzero)
      have hab:∀ᶠb in 𝓝 (0:ℂ),‖a+b‖<r:=
        (continuous_const.add continuous_id).norm.continuousAt
          (isOpen_Iio.mem_nhds (by simpa only [add_zero] using har))
      filter_upwards [hb,hab] with b hb hab
      exact hm a b har hb hab
    have hl:HasDerivAt (fun b:ℂ=>R (a+b)*R 0) (deriv R a*R 0) 0:=by
      simpa only [add_zero,mul_one] using
        (((hd a har).hasDerivAt.comp 0 ((hasDerivAt_id (0:ℂ)).const_add a)).mul_const (R 0))
    have hr':HasDerivAt (fun b:ℂ=>R a*R b) (R a*deriv R 0) 0:=
      ((hd 0 hzero).hasDerivAt).const_mul (R a)
    have hh:deriv R a*R 0=R a*deriv R 0:=
      (hl.congr_of_eventuallyEq hs.symm).unique hr'
    dsimp only [l]
    field_simp [h0]
    simpa only [mul_comm] using hh
  let W:ℂ→ℂ:=fun t=>R t*Complex.exp (-l*t)
  have hW:∀t:ℂ,‖t‖<r/2→HasDerivAt W 0 t:=by
    intro t ht
    have ht':‖t‖<r:=lt_trans ht (by linarith)
    have hexp:HasDerivAt (fun s:ℂ=>Complex.exp (-l*s))
        (Complex.exp (-l*t)*(-l)) t:=
      (((hasDerivAt_id t).const_mul (-l)).cexp)
    have h:=((hd t ht').hasDerivAt).mul hexp
    rw [heq t ht] at h
    convert h using 1 <;> ring
  have hdW:DifferentiableOn ℂ W (ball 0 (r/2)):=by
    intro t ht
    exact (hW t (by simpa only [mem_ball,dist_zero_right] using ht)).differentiableAt.differentiableWithinAt
  have hzW:(ball (0:ℂ) (r/2)).EqOn (deriv W) 0:=by
    intro t ht
    exact (hW t (by simpa only [mem_ball,dist_zero_right] using ht)).deriv
  have hcenter:(0:ℂ)∈ball 0 (r/2):=mem_ball_self (by linarith)
  filter_upwards [isOpen_ball.mem_nhds hcenter] with t ht
  have hc:=isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0:ℂ) (r/2)).isPreconnected
    hdW hzW ht hcenter
  have he:R t*Complex.exp (-l*t)=R 0:=by simpa only [W,mul_zero,Complex.exp_zero,mul_one] using hc
  calc
    R t=(R t*Complex.exp (-l*t))*Complex.exp (l*t):=by
      rw [mul_assoc,←Complex.exp_add,neg_mul,neg_add_cancel,Complex.exp_zero,mul_one]
    _=R 0*Complex.exp (l*t):=by rw [he]
end LocalMultiplicativeGerm318
