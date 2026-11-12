module
public import Mathlib.Tactic
public section
namespace PELDirichletPolygonCertificate318
set_option maxHeartbeats 1600000

/-- Exact rational certificate for the first-quadrant Dirichlet polygon.
The original disk coordinates are a/√1050 and b/√5. No numeric polygon
computation or unproved fundamental-domain assertion is used here. -/
theorem polygon_bound (a b : ℝ) (ha : 0≤a) (hb : 0≤b)
    (h0 : a≤420/13) (h1 : a≤(-45/17)*b+555/17)
    (h2 : a≤(-210/43)*b+1470/43) (h3 : a≤ -6*b+35)
    (h4 : a≤(-210/29)*b+1050/29) (h5 : a≤(-17/2)*b+75/2)
    (h6 : a≤(-165/13)*b+555/13) (h7 : b≤5/3) :
    a^2/1050+b^2/5≤9999/10000 := by
  have sqbound (t : ℝ) (ht : a≤t) : a^2≤t^2 := by
    have hplus : 0≤t+a := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) hplus]
  by_cases hB0 : b≤5/39
  · have hs := sqbound (420/13) h0
    have hb2 := mul_nonneg hb (sub_nonneg.mpr hB0)
    nlinarith
  · by_cases hB1 : b≤75/109
    · have hs := sqbound ((-45/17)*b+555/17) h1
      have hb2 := mul_nonneg (by linarith : 0≤b-5/39) (sub_nonneg.mpr hB1)
      nlinarith
    · by_cases hB2 : b≤35/48
      · have hs := sqbound ((-210/43)*b+1470/43) h2
        have hb2 := mul_nonneg (by linarith : 0≤b-75/109) (sub_nonneg.mpr hB2)
        nlinarith
      · by_cases hB3 : b≤35/36
        · have hs := sqbound (-6*b+35) h3
          have hb2 := mul_nonneg (by linarith : 0≤b-35/48) (sub_nonneg.mpr hB3)
          nlinarith
        · by_cases hB4 : b≤75/73
          · have hs := sqbound ((-210/29)*b+1050/29) h4
            have hb2 := mul_nonneg (by linarith : 0≤b-35/36) (sub_nonneg.mpr hB4)
            nlinarith
          · by_cases hB5 : b≤135/109
            · have hs := sqbound ((-17/2)*b+75/2) h5
              have hb2 := mul_nonneg (by linarith : 0≤b-75/73) (sub_nonneg.mpr hB5)
              nlinarith
            · have hs := sqbound ((-165/13)*b+555/13) h6
              have hb2 := mul_nonneg (by linarith : 0≤b-135/109) (sub_nonneg.mpr h7)
              nlinarith

/-- A sign-complete family of literal halfplanes controls the absolute
coordinates. This keeps all four quadrants in the eventual source coverage. -/
theorem absolute_halfplane (a b c u v : ℝ)
    (h : ∀ ε δ : ℝ, (ε=1 ∨ ε= -1) → (δ=1 ∨ δ= -1) → u*(ε*a)+v*(δ*b)≤c) :
    u*|a|+v*|b|≤c := by
  by_cases ha : 0≤a <;> by_cases hb : 0≤b
  · simpa only [abs_of_nonneg ha,abs_of_nonneg hb,one_mul] using h 1 1 (Or.inl rfl) (Or.inl rfl)
  · simpa only [abs_of_nonneg ha,abs_of_neg (lt_of_not_ge hb),one_mul,neg_one_mul]
      using h 1 (-1) (Or.inl rfl) (Or.inr rfl)
  · simpa only [abs_of_neg (lt_of_not_ge ha),abs_of_nonneg hb,one_mul,neg_one_mul]
      using h (-1) 1 (Or.inr rfl) (Or.inl rfl)
  · simpa only [abs_of_neg (lt_of_not_ge ha),abs_of_neg (lt_of_not_ge hb),neg_one_mul]
      using h (-1) (-1) (Or.inr rfl) (Or.inr rfl)
end PELDirichletPolygonCertificate318
