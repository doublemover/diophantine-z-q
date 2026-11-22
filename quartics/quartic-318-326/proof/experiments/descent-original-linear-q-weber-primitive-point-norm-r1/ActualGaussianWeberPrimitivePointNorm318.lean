module
public import ActualGaussianWeberSameValueOrbit318
public import ActualGaussianWeberEvenNormLift318
public section

namespace ActualGaussianWeberPrimitivePointNorm318

open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberQuarterTurn318
open ActualGaussianWeberSameValueOrbit318 ActualGaussianWeberEvenNormLift318

variable {K : Type*} [Field K] [DecidableEq K]

/-- Positive part of the original Weber kernel, on just the original primitive
point. If one actual Gaussian scalar fixes its Weber value, the norm is one
modulo twice the even level. Only the separating half of primitivity is used;
neither an action on the full torsion field nor surjectivity of a ray
representation is a hypothesis of this local statement. -/
theorem norm_one_of_fixed_primitive_value (h2 : (2:K) ≠ 0)
    (i : K) (hi : i^2 = -1) (M : ℤ) (hM : Even M) (P : WP K)
    (hPrimitive : ∀ c d : ℤ, c • P+d • turn h2 i hi P=0 → M ∣ c ∧ M ∣ d)
    (a b p : ℤ) (hNorm : a^2+b^2=p)
    (hValue : squaredAbscissa (a • P+b • turn h2 i hi P)=squaredAbscissa P) :
    2 * M ∣ p - 1 := by
  let J := turn h2 i hi P
  have compareUnit (c d : ℤ) (hc : c^2+d^2=1)
      (h : a • P+b • J=c • P+d • J) : 2 * M ∣ p - 1 := by
    have h0 : (a-c) • P+(b-d) • J=0 := by
      calc
        _ = (a • P+b • J)-(c • P+d • J) := by
          simp only [sub_zsmul]
          abel
        _ = 0 := sub_eq_zero.mpr h
    obtain ⟨hc',hd'⟩ := hPrimitive (a-c) (b-d) h0
    have hCongruence := norm_even_congr M a b c d hM hc' hd'
    rw [hNorm,hc] at hCongruence
    exact hCongruence
  rcases (same_weber_value h2 i hi P (a • P+b • J)).mp hValue with h|h|h|h
  · exact compareUnit 1 0 (by norm_num) (by
      simpa only [one_zsmul,zero_zsmul,add_zero] using h)
  · exact compareUnit (-1) 0 (by norm_num) (by
      simpa only [neg_zsmul,one_zsmul,zero_zsmul,add_zero] using h)
  · exact compareUnit 0 1 (by norm_num) (by
      simpa only [zero_zsmul,one_zsmul,zero_add] using h)
  · exact compareUnit 0 (-1) (by norm_num) (by
      simpa only [zero_zsmul,neg_zsmul,one_zsmul,zero_add] using h)

end ActualGaussianWeberPrimitivePointNorm318
