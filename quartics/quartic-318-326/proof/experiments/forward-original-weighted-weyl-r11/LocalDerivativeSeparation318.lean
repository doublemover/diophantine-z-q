module
public import AlgebraicFormalSubgroup318
public import UnitPlaceOddSigns318
public section
noncomputable section
namespace LocalDerivativeSeparation318
open ReciprocalDouble318 WeierstrassCurve.Affine
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [CharZero F]

/-- Exact discriminant identity at an actual short-curve point. It controls
both possible local difference slopes even at a bad reduction place. -/
lemma discriminant_identity (D x y : F) (hc : y^2=x^3-D*x) :
    4*D^3=(4*D-3*x^2)*(3*x^2-D)^2+27*y^4 := by
  linear_combination -27*(y^2+x^3-D*x)*hc

lemma derivative_or_ordinate (D x y : F) (hD : D≠0) (hc : y^2=x^3-D*x) :
    y≠0 ∨ 3*x^2-D≠0 := by
  by_cases hy : y=0
  · right
    intro hg
    have he := discriminant_identity D x y hc
    have hz : 4*D^3=0 := by
      simpa only [hy,hg,zero_pow (by decide : 2≠0),
        zero_pow (by decide : 4≠0),mul_zero,zero_add] using he
    exact (mul_ne_zero (by norm_num : (4:F)≠0) (pow_ne_zero 3 hD)) hz
  · exact Or.inl hy

variable (w : AbsoluteValue F ℝ) (hna : IsNonarchimedean w)
include hna
lemma nat_le_one (n : ℕ) : w (n:F)≤1 :=
  hna.apply_natCast_le_one (map_zero_le w 1) (map_one w)

/-- Nonformal affine coordinates form a bounded set in a complete local
field: integral x and D force integral y. -/
lemma ordinate_integral (D x y : F) (hD : w D≤1) (hx : w x≤1)
    (hc : y^2=x^3-D*x) : w y≤1 := by
  have hpower : w (x^3)≤1 := by
    rw [map_pow]
    exact pow_le_one₀ (apply_nonneg w x) hx
  have hproduct : w (D*x)≤1 := by
    rw [map_mul]
    exact mul_le_one₀ hD (apply_nonneg w x) hx
  have hbound := (hna (x^3) (-(D*x))).trans (max_le hpower (by simpa using hproduct))
  rw [←sub_eq_add_neg,←hc,map_pow] at hbound
  nlinarith [apply_nonneg w y]

/-- A quantitative non-simultaneous-smallness bound for the two local
slopes. The positive left side includes the actual bad-place discriminant,
so this does not silently assume good reduction. -/
theorem derivative_bound (D x y : F) (hD : w D≤1) (hx : w x≤1)
    (hc : y^2=x^3-D*x) :
    w (4*D^3)≤max ((w (3*x^2-D))^2) ((w y)^4) := by
  have h4 := nat_le_one w hna 4
  have h3 := nat_le_one w hna 3
  have h27 := nat_le_one w hna 27
  have hx2 : w (x^2)≤1 := by rw [map_pow]; exact pow_le_one₀ (apply_nonneg w x) hx
  have hleft : w (4*D)≤1 := by
    rw [map_mul]
    exact mul_le_one₀ h4 (apply_nonneg w D) hD
  have hright : w (3*x^2)≤1 := by
    rw [map_mul]
    exact mul_le_one₀ h3 (apply_nonneg w (x^2)) hx2
  have hcoef : w (4*D-3*x^2)≤1 := by
    simpa only [sub_eq_add_neg,map_neg_eq_map] using
      (hna (4*D) (-(3*x^2))).trans (max_le hleft (by simpa using hright))
  rw [discriminant_identity D x y hc]
  have he := hna ((4*D-3*x^2)*(3*x^2-D)^2) (27*y^4)
  rw [map_mul,map_mul,map_pow,map_pow] at he
  apply he.trans
  exact max_le_max
    (mul_le_of_le_one_left (sq_nonneg _) hcoef)
    (mul_le_of_le_one_left (pow_nonneg (apply_nonneg w y) _) h27)

/-- Once either exact difference slope is larger than one, the chord
abscissa is a formal pole. This is the local target needed for finite
residue coding; actual point identities are kept for the next module. -/
lemma slope_pole (x₁ x₂ slope : F) (hx₁ : w x₁≤1) (hx₂ : w x₂≤1)
    (hs : 1<w slope) : 1<w (slope^2-x₁-x₂) := by
  have hsum : w (x₁+x₂)≤1 := (hna x₁ x₂).trans (max_le hx₁ hx₂)
  have hsquare : 1<w (slope^2) := by rw [map_pow]; nlinarith
  have he := hna.add_eq_left_of_lt (map_neg_eq_map w)
    (show w (-(x₁+x₂))<w (slope^2) by simpa only [map_neg_eq_map] using hsum.trans_lt hsquare)
  have hi : slope^2-x₁-x₂=slope^2+ -(x₁+x₂) := by ring
  rw [hi,he]
  exact hsquare

end LocalDerivativeSeparation318
