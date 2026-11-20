module
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public section

namespace CTComplexUnitNorm318

/-- The image of the literal complex conjugation norm is exactly
the positive real scalars. No topological coefficient choice is used. -/
theorem conj_mul_exists_iff (z : ℂ) :
    (∃ u : ℂˣ, (starRingEnd ℂ) (u : ℂ) * (u : ℂ) = z) ↔
      ∃ r : ℝ, 0 < r ∧ (r : ℂ) = z := by
  constructor
  · rintro ⟨u,hu⟩
    exact ⟨Complex.normSq (u : ℂ),
      Complex.normSq_pos.mpr (Units.ne_zero u),
      Complex.normSq_eq_conj_mul_self.trans hu⟩
  · rintro ⟨r,hr,rfl⟩
    have hS : Real.sqrt r ≠ 0 := Real.sqrt_ne_zero'.2 hr
    have hC : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 := by
      simpa only [Complex.ofReal_eq_zero] using hS
    refine ⟨Units.mk0 ((Real.sqrt r : ℝ) : ℂ) hC,?_⟩
    change (starRingEnd ℂ) ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ) = (r : ℂ)
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_ofReal,Real.mul_self_sqrt hr.le]

/-- Among conjugation-fixed nonzero values, membership in the norm
subgroup is precisely the positive real branch. -/
theorem conj_fixed_norm_iff (z : ℂˣ) (hz : (starRingEnd ℂ) (z : ℂ) = (z : ℂ)) :
    (∃ u : ℂˣ, (starRingEnd ℂ) (u : ℂ) * (u : ℂ) = (z : ℂ)) ↔
      0 < (z : ℂ).re := by
  rw [conj_mul_exists_iff]
  constructor
  · rintro ⟨r,hr,hrz⟩
    have he : r = (z : ℂ).re := by
      simpa only [Complex.ofReal_re] using congrArg Complex.re hrz
    rwa [← he]
  · intro h
    exact ⟨(z : ℂ).re,h,Complex.conj_eq_iff_re.mp hz⟩

end CTComplexUnitNorm318
