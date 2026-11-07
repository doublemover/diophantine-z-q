module
public import WeierstrassODE318
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public section
noncomputable section
open Filter Set
open scoped Topology
namespace WeierstrassImmersion318
open PeriodEisenstein318 LatticeInvariants318 ModularWeierstrass318
set_option maxHeartbeats 0

lemma lattice_discriminant (tau : UpperHalfPlane) :
    (periods tau).g₂ ^ 3 - 27 * (periods tau).g₃ ^ 2 =
      4096 * (Real.pi : ℂ) ^ 12 * ModularForm.discriminant tau := by
  rw [g2_normalization, g3_normalization, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  ring

lemma lattice_discriminant_ne_zero (tau : UpperHalfPlane) :
    (periods tau).g₂ ^ 3 - 27 * (periods tau).g₃ ^ 2 ≠ 0 := by
  rw [lattice_discriminant]
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (ModularForm.discriminant_ne_zero tau)

/-- At least one coordinate of the actual Weierstrass pair has nonzero derivative. -/
theorem pair_derivative_nonzero (tau : UpperHalfPlane) (z : ℂ)
    (hz : z ∉ (periods tau).lattice) :
    (periods tau).derivWeierstrassP z ≠ 0 ∨
      deriv (periods tau).derivWeierstrassP z ≠ 0 := by
  by_contra h
  push Not at h
  have h2 := WeierstrassODE318.second_derivative (periods tau) z hz
  have h3 := (periods tau).derivWeierstrassP_sq z hz
  have hg2 : (periods tau).g₂ = 12 * (periods tau).weierstrassP z ^ 2 := by
    rw [h.2] at h2
    linear_combination 2 * h2
  have hg3 : (periods tau).g₃ = -8 * (periods tau).weierstrassP z ^ 3 := by
    rw [h.1, hg2] at h3
    linear_combination h3
  apply lattice_discriminant_ne_zero tau
  rw [hg2, hg3]
  ring

/-- Local scalar injectivity from the actual analytic derivative and inverse theorem. -/
lemma analytic_local_injective {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hderiv : deriv f z ≠ 0) : ∃ U ∈ 𝓝 z, Set.InjOn f U := by
  have hi := hf.hasStrictDerivAt.eventually_left_inverse hderiv
  refine ⟨{w | hf.hasStrictDerivAt.localInverse f (deriv f z) z hderiv (f w) = w}, hi, ?_⟩
  intro a ha b hb he
  rw [← ha, ← hb, he]

/-- The actual pair (℘,℘') is injective on some neighborhood of each non-lattice point.
This does not assert global injectivity modulo the period lattice. -/
theorem pair_local_injective (tau : UpperHalfPlane) (z : ℂ)
    (hz : z ∉ (periods tau).lattice) :
    ∃ U ∈ 𝓝 z, Set.InjOn
      (fun w => ((periods tau).weierstrassP w, (periods tau).derivWeierstrassP w)) U := by
  rcases pair_derivative_nonzero tau z hz with h | h
  · have hd : deriv (periods tau).weierstrassP z ≠ 0 := by simpa using h
    obtain ⟨U, hU, hi⟩ := analytic_local_injective
      ((periods tau).analyticOnNhd_weierstrassP z hz) hd
    exact ⟨U, hU, fun a ha b hb he => hi ha hb (congrArg Prod.fst he)⟩
  · obtain ⟨U, hU, hi⟩ := analytic_local_injective
      ((periods tau).analyticOnNhd_derivWeierstrassP z hz) h
    exact ⟨U, hU, fun a ha b hb he => hi ha hb (congrArg Prod.snd he)⟩

end WeierstrassImmersion318
