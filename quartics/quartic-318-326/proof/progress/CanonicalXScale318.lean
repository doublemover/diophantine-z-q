module
public import OpenJLocalPointMaps318
public section
noncomputable section
namespace CanonicalXScale318
open OpenJComplexEvaluation318 OpenJLocalComparison318
set_option maxHeartbeats 0

/-- The sign-independent x-coordinate scale, defined only from the actual
coefficient functions and not from a choice of square root. -/
@[expose] def scale (z : ℂ) : ℂ := LocalShortScaling318.ratio A B C D z

lemma fiber_coefficients_at (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    (fiber N tau h).a₄=A (tau:ℂ) ∧ (fiber N tau h).a₆=B (tau:ℂ) := by
  simpa using fiber_coefficients N (tau:ℂ) (by simpa using h)

lemma scale_eq_square (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau)
    (u : ℂˣ)
    (h4 : (ModularWeierstrass318.curve tau).a₄=(u:ℂ)^4*(fiber N tau h).a₄)
    (h6 : (ModularWeierstrass318.curve tau).a₆=(u:ℂ)^6*(fiber N tau h).a₆) :
    scale (tau:ℂ)=(u:ℂ)^2 := by
  have hc := fiber_coefficients_at N tau h
  apply LocalShortScaling318.ratio_of_scaling A B C D (tau:ℂ) u
  · rw [←hc.1]; exact OpenJScalingAmbiguity318.fiber_a4_ne_zero N tau h
  · rw [←hc.2]; exact OpenJScalingAmbiguity318.fiber_a6_ne_zero N tau h
  · simpa [C,hc.1] using h4
  · simpa [D,hc.2] using h6

lemma scale_ne_zero (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    scale (tau:ℂ)≠0 := by
  rw [scale_eq_square N tau h (OpenJAnalyticPoints318.scaling N tau h)
    (OpenJAnalyticPoints318.scaling_spec N tau h).1
    (OpenJAnalyticPoints318.scaling_spec N tau h).2]
  exact pow_ne_zero 2 (Units.ne_zero _)

/-- The x-scale is holomorphic on the actual admissible upper-half-plane
locus, without any square-root branch choice. -/
theorem scale_analyticAt (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    AnalyticAt ℂ scale (tau:ℂ) := by
  have hc := coefficient_analyticAt tau h
  have hf := fiber_coefficients_at N tau h
  have hA : A (tau:ℂ)≠0 := hf.1 ▸ OpenJScalingAmbiguity318.fiber_a4_ne_zero N tau h
  have hB : B (tau:ℂ)≠0 := hf.2 ▸ OpenJScalingAmbiguity318.fiber_a6_ne_zero N tau h
  have hC : C (tau:ℂ)≠0 := by
    have he := (OpenJAnalyticPoints318.scaling_spec N tau h).1
    have hn : (ModularWeierstrass318.curve tau).a₄≠0 := by
      rw [he]
      exact mul_ne_zero (pow_ne_zero 4 (Units.ne_zero _))
        (OpenJScalingAmbiguity318.fiber_a4_ne_zero N tau h)
    simpa [C] using hn
  exact (hc.2.2.2.div hc.2.1 hB).div (hc.2.2.1.div hc.1 hA) (div_ne_zero hC hA)

/-- The fourth/sixth-power coefficient comparison descends to the canonical
square/cube comparison on x-coordinates. -/
theorem coefficient_comparison (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    (ModularWeierstrass318.curve tau).a₄=scale (tau:ℂ)^2*(fiber N tau h).a₄ ∧
    (ModularWeierstrass318.curve tau).a₆=scale (tau:ℂ)^3*(fiber N tau h).a₆ := by
  have hs := OpenJAnalyticPoints318.scaling_spec N tau h
  rw [scale_eq_square N tau h (OpenJAnalyticPoints318.scaling N tau h) hs.1 hs.2]
  constructor
  · convert hs.1 using 1 <;> ring
  · convert hs.2 using 1 <;> ring

end CanonicalXScale318
