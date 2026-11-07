module
public import SectionHeight318
public import RationalAbsoluteHeight
public section
noncomputable section
open NumberField Height Real
namespace SectionHeight318
set_option maxHeartbeats 0
variable {K : Type*} [Field K] [NumberField K]

/-- The actual relative height of a rational number is its rational height
multiplied by the extension degree. -/
theorem logHeight_ratCast (q : ℚ) :
    Height.logHeight₁ (q : K) =
      (Module.finrank ℚ K : ℝ) * Height.logHeight₁ q := by
  rw [Height.logHeight₁_eq_log_mulHeight₁, RationalAbsoluteHeight.mulHeight_ratCast,
    Real.log_pow, Rat.logHeight₁_eq_log_max]
  simp only [Nat.cast_max]

/-- The exact NumberField-to-rational comparison needed for the contact map. -/
theorem rational_ratio_height (a₀ a₁ : K) (q : ℚ) (ha₀ : a₀ ≠ 0)
    (hrel : a₁ = (q : K) * a₀) :
    Height.logHeight ![a₀, a₁] / (Module.finrank ℚ K : ℝ) = Height.logHeight₁ q := by
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hdiv : a₁ / a₀ = (q : K) := (div_eq_iff ha₀).mpr hrel
  rw [Height.logHeight_swap, ← Height.logHeight₁_div_eq_logHeight a₁ a₀,
    hdiv, logHeight_ratCast, mul_div_cancel_left₀ _ hd]

/-- Integral sections with rational ratio give the actual rational height bound.
No degree/base-change equality or final height bound is assumed. -/
theorem rational_section_height (a₀ a₁ : K) (q : ℚ) (ha₀ : a₀ ≠ 0)
    (hrel : a₁ = (q : K) * a₀) (F : FrameNorms K) (C : ℝ)
    (harch : ∀ (v : InfinitePlace K) i, v (![a₀, a₁] i) * F.arch v ≤ C)
    (hfinite : ∀ (v : FinitePlace K) i, v (![a₀, a₁] i) * F.finiteNorm v ≤ 1) :
    Height.logHeight₁ q ≤ F.normalizedDegree + Real.log C := by
  have ha : (![a₀, a₁] : Fin 2 → K) ≠ 0 := by
    intro he
    exact ha₀ (by simpa using congrFun he 0)
  have h := section_height ha F C harch hfinite
  unfold absoluteProjectiveHeight at h
  rw [Projectivization.logHeight_mk, rational_ratio_height a₀ a₁ q ha₀ hrel] at h
  exact h

end SectionHeight318
