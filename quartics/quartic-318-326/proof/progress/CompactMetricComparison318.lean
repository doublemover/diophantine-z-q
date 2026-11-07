module
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic
public section
noncomputable section
open Filter Set
open scoped Topology
namespace CompactMetricComparison318
set_option maxHeartbeats 0

/-- The second derivative at a continuous local maximum is nonpositive.
This is derived from actual derivative calculus, not supplied as a premise. -/
theorem second_deriv_nonpos_of_localMax {f : ℝ → ℝ} {x : ℝ}
    (hc : ContinuousAt f x) (hm : IsLocalMax f x) : deriv (deriv f) x ≤ 0 := by
  by_contra! hp
  have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm, hmin] with y hy hy'
    exact le_antisymm hy hy'
  have hdd := he.deriv.deriv_eq
  simp only [deriv_const', deriv_const] at hdd
  linarith

/-- The ordinary two-real-coordinate Laplacian at the chart origin. -/
@[expose] def laplacianAtOrigin (f : ℝ × ℝ → ℝ) : ℝ :=
  deriv (deriv (fun t : ℝ => f (t, 0))) 0 +
  deriv (deriv (fun t : ℝ => f (0, t))) 0

/-- A continuous actual coordinate function has nonpositive Laplacian
at a local maximum. Smoothness is unnecessary for this total-derivative form. -/
theorem laplacian_nonpos_of_localMax {f : ℝ × ℝ → ℝ}
    (hc : ContinuousAt f (0, 0)) (hm : IsLocalMax f (0, 0)) :
    laplacianAtOrigin f ≤ 0 := by
  have hx : ContinuousAt (fun t : ℝ => (t, (0 : ℝ))) 0 := by fun_prop
  have hy : ContinuousAt (fun t : ℝ => ((0 : ℝ), t)) 0 := by fun_prop
  have hmx : IsLocalMax (fun t : ℝ => f (t, 0)) 0 := by
    exact hm.comp_continuous (g := fun t : ℝ => (t, (0 : ℝ))) hx
  have hmy : IsLocalMax (fun t : ℝ => f (0, t)) 0 := by
    exact hm.comp_continuous (g := fun t : ℝ => ((0 : ℝ), t)) hy
  exact add_nonpos (second_deriv_nonpos_of_localMax (hc.comp (f := fun t : ℝ => (t, (0 : ℝ))) hx) hmx)
    (second_deriv_nonpos_of_localMax (hc.comp (f := fun t : ℝ => ((0 : ℝ), t)) hy) hmy)

/-- Exact local curvature arithmetic for the source ratio rho/(C*h).
The density rho at the point is C*h*r, and h has curvature minus one. -/
theorem curvature_forces_positive_laplacian (C h r k L : ℝ)
    (hC : 0 < C) (hh : 0 < h) (hr : 1 < r)
    (hk : k ≤ -1 / C)
    (hL : L = -2 * k * (C * h * r) - 2 * h) : 0 < L := by
  have hk' : k * C ≤ -1 := (le_div_iff₀ hC).mp hk
  have hhr : 0 ≤ h * r := by positivity
  have hm := mul_le_mul_of_nonneg_right hk' hhr
  have hp : 0 < 2 * h * (r - 1) := by positivity
  rw [hL]
  nlinarith

/-- Compact maximum-principle comparison for the actual positive ratio.
The chart maps, continuity, actual Laplacian/curvature identity, and curvature
upper bound are explicit. No maximum-principle or Laplacian-sign input occurs. -/
theorem compact_ratio_le_one {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] (ratio : X → ℝ) (hcontinuous : Continuous ratio)
    (hpositive : ∀ x, 0 < ratio x) (C : ℝ) (hC : 0 < C)
    (chart : X → ℝ × ℝ → X) (chart_origin : ∀ x, chart x (0, 0) = x)
    (chart_continuous : ∀ x, ContinuousAt (chart x) (0, 0))
    (hyperbolic curvature : X → ℝ) (hhyperbolic : ∀ x, 0 < hyperbolic x)
    (hcurvature : ∀ x, curvature x ≤ -1 / C)
    (curvature_identity : ∀ x,
      laplacianAtOrigin (fun z => Real.log (ratio (chart x z))) =
        -2 * curvature x * (C * hyperbolic x * ratio x) - 2 * hyperbolic x) :
    ∀ x, ratio x ≤ 1 := by
  obtain ⟨x, _, hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set X).Nonempty) hcontinuous.continuousOn
  have htop : ratio x ≤ 1 := by
    by_contra! hx
    have hmaxlog : IsLocalMax (fun z => Real.log (ratio (chart x z))) (0, 0) := by
      apply Filter.Eventually.of_forall
      intro z
      change Real.log (ratio (chart x z)) ≤ Real.log (ratio (chart x (0, 0)))
      rw [chart_origin]
      exact Real.log_le_log (hpositive _) (hmax (Set.mem_univ _))
    have hc : ContinuousAt (fun z => Real.log (ratio (chart x z))) (0, 0) := by
      apply ContinuousAt.log
      · exact hcontinuous.continuousAt.comp (chart_continuous x)
      · exact (hpositive _).ne'
    have hn := laplacian_nonpos_of_localMax hc hmaxlog
    have hp := curvature_forces_positive_laplacian C (hyperbolic x) (ratio x)
      (curvature x) _ hC (hhyperbolic x) hx (hcurvature x) (curvature_identity x)
    linarith
  intro y
  exact (hmax (Set.mem_univ y)).trans htop

/-- The source metric inequality in its literal rho <= C*h form. -/
theorem compact_metric_comparison {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] (rho hyperbolic : X → ℝ)
    (hrho : ∀ x, 0 < rho x) (hhyperbolic : ∀ x, 0 < hyperbolic x)
    (C : ℝ) (hC : 0 < C)
    (hcontinuous : Continuous (fun x => rho x / (C * hyperbolic x)))
    (chart : X → ℝ × ℝ → X) (chart_origin : ∀ x, chart x (0, 0) = x)
    (chart_continuous : ∀ x, ContinuousAt (chart x) (0, 0))
    (curvature : X → ℝ) (hcurvature : ∀ x, curvature x ≤ -1 / C)
    (curvature_identity : ∀ x,
      laplacianAtOrigin (fun z => Real.log (rho (chart x z) / (C * hyperbolic (chart x z)))) =
        -2 * curvature x * rho x - 2 * hyperbolic x) :
    ∀ x, rho x ≤ C * hyperbolic x := by
  have hb := compact_ratio_le_one (fun x => rho x / (C * hyperbolic x)) hcontinuous
    (fun x => div_pos (hrho x) (mul_pos hC (hhyperbolic x))) C hC chart chart_origin
    chart_continuous hyperbolic curvature hhyperbolic hcurvature ?_
  · intro x
    exact (div_le_one (mul_pos hC (hhyperbolic x))).mp (hb x)
  · intro x
    rw [curvature_identity]
    have hd : C * hyperbolic x ≠ 0 := (mul_pos hC (hhyperbolic x)).ne'
    rw [mul_div_cancel₀ _ hd]

end CompactMetricComparison318
#print axioms CompactMetricComparison318.second_deriv_nonpos_of_localMax
#print axioms CompactMetricComparison318.laplacian_nonpos_of_localMax
#print axioms CompactMetricComparison318.curvature_forces_positive_laplacian
#print axioms CompactMetricComparison318.compact_ratio_le_one
#print axioms CompactMetricComparison318.compact_metric_comparison
