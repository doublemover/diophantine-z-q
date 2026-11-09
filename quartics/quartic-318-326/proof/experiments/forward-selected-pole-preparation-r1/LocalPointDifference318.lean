module
public import LocalDerivativeSeparation318
public section
noncomputable section
namespace LocalPointDifference318
open ReciprocalDouble318 WeierstrassCurve.Affine
open LocalDerivativeSeparation318
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

lemma difference_curve (D x₁ y₁ x₂ y₂ : F)
    (h₁ : y₁^2=x₁^3-D*x₁) (h₂ : y₂^2=x₂^3-D*x₂) :
    (y₂-y₁)*(y₂+y₁)=(x₂-x₁)*(x₁^2+x₁*x₂+x₂^2-D) := by
  linear_combination h₂-h₁

lemma alternative_slope (D x₁ y₁ x₂ y₂ : F) (hx : x₁≠x₂) (hy : y₁≠y₂)
    (h₁ : y₁^2=x₁^3-D*x₁) (h₂ : y₂^2=x₂^3-D*x₂) :
    (y₁+y₂)/(x₁-x₂)= -(x₁^2+x₁*x₂+x₂^2-D)/(y₂-y₁) := by
  apply (div_eq_div_iff (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hy.symm)).mpr
  linear_combination difference_curve D x₁ y₁ x₂ y₂ h₁ h₂

lemma derivative_difference (D x₁ x₂ : F) :
    (x₁^2+x₁*x₂+x₂^2-D)-(3*x₁^2-D)=(x₂-x₁)*(2*x₁+x₂) := by ring

/-- Exact actual secant abscissa for P−Q, not a detached chord polynomial. -/
lemma difference_x (D x₁ y₁ x₂ y₂ : F) (hx : x₁≠x₂)
    (h₁ : (E D).Nonsingular x₁ y₁) (h₂ : (E D).Nonsingular x₂ y₂) :
    (Point.some x₁ y₁ h₁-Point.some x₂ y₂ h₂).xRep 0=
      ((y₁+y₂)/(x₁-x₂))^2-x₁-x₂ := by
  rw [sub_eq_add_neg,Point.neg_some,Point.add_of_X_ne hx]
  simp only [Point.xRep_some,Matrix.cons_val_zero,addX,slope_of_X_ne hx,
    negY,E,zero_mul,mul_zero,add_zero,sub_zero,sub_neg_eq_add]

variable (w : AbsoluteValue F ℝ) (hna : IsNonarchimedean w)

/-- Either exact slope estimate implies actual formal membership of the
secant difference, including a nonzero affine output with x-pole. -/
theorem secant_formal (D x₁ y₁ x₂ y₂ : F) (hD : w D≤1)
    (h₁ : (E D).Nonsingular x₁ y₁) (h₂ : (E D).Nonsingular x₂ y₂)
    (hx : x₁≠x₂) (hx₁ : w x₁≤1) (hx₂ : w x₂≤1)
    (hs : w (x₁-x₂)<w (y₁+y₂)) :
    Point.some x₁ y₁ h₁-Point.some x₂ y₂ h₂∈
      AlgebraicFormalSubgroup318.formalSubgroup w hna D hD := by
  apply Or.inr
  rw [difference_x D x₁ y₁ x₂ y₂ hx h₁ h₂]
  apply slope_pole w hna x₁ x₂ _ hx₁ hx₂
  rw [map_div₀]
  exact (one_lt_div (w.pos (sub_ne_zero.mpr hx))).mpr hs

/-- In the nonzero-ordinate chart, closeness in both original affine
coordinates forces the secant into the formal neighborhood. -/
theorem close_ordinate_secant (D x₁ y₁ x₂ y₂ : F) (hD : w D≤1)
    (h₁ : (E D).Nonsingular x₁ y₁) (h₂ : (E D).Nonsingular x₂ y₂)
    (hx : x₁≠x₂) (hx₁ : w x₁≤1) (hx₂ : w x₂≤1)
    (hdx : w (x₁-x₂)<w (2*y₁)) (hdy : w (y₂-y₁)<w (2*y₁)) :
    Point.some x₁ y₁ h₁-Point.some x₂ y₂ h₂∈
      AlgebraicFormalSubgroup318.formalSubgroup w hna D hD := by
  have he : w (y₁+y₂)=w (2*y₁) := by
    rw [show y₁+y₂=2*y₁+(y₂-y₁) by ring]
    exact hna.add_eq_left_of_lt (map_neg_eq_map w) hdy
  exact secant_formal w hna D x₁ y₁ x₂ y₂ hD h₁ h₂ hx hx₁ hx₂ (by rw [he]; exact hdx)

/-- The derivative chart handles small ordinates, including bad reduction.
The auxiliary numerator is compared to the exact derivative at the center;
its nonvanishing forces the alternate slope denominator to be nonzero. -/
theorem close_derivative_secant (D x₁ y₁ x₂ y₂ : F) (hD : w D≤1)
    (h₁ : (E D).Nonsingular x₁ y₁) (h₂ : (E D).Nonsingular x₂ y₂)
    (hx : x₁≠x₂) (hx₁ : w x₁≤1) (hx₂ : w x₂≤1)
    (hdx : w (x₂-x₁)<w (3*x₁^2-D))
    (hdy : w (y₂-y₁)<w (3*x₁^2-D)) :
    Point.some x₁ y₁ h₁-Point.some x₂ y₂ h₂∈
      AlgebraicFormalSubgroup318.formalSubgroup w hna D hD := by
  let g := 3*x₁^2-D
  let b := x₁^2+x₁*x₂+x₂^2-D
  have hcoeff : w (2*x₁+x₂)≤1 := by
    apply (hna _ _).trans
    apply max_le _ hx₂
    rw [map_mul]
    exact mul_le_one₀ (nat_le_one w hna 2) (apply_nonneg w x₁) hx₁
  have hdiff : w (b-g)<w g := by
    rw [show b-g=(x₂-x₁)*(2*x₁+x₂) from derivative_difference D x₁ x₂,map_mul]
    exact (mul_le_of_le_one_right (apply_nonneg w _) hcoeff).trans_lt hdx
  have hb : w b=w g := by
    calc
      w b = w (g+(b-g)) := by congr 1; ring
      _ = w g := hna.add_eq_left_of_lt (map_neg_eq_map w) hdiff
  have hb0 : b≠0 := by
    apply w.pos_iff.mp
    rw [hb]
    exact lt_of_le_of_lt (apply_nonneg w _) hdx
  have hcurve := difference_curve D x₁ y₁ x₂ y₂
    (FormalChartDouble.ordinate_equation D x₁ y₁ h₁)
    (FormalChartDouble.ordinate_equation D x₂ y₂ h₂)
  have hy : y₁≠y₂ := by
    intro he
    rw [he,sub_self,zero_mul] at hcurve
    exact (mul_ne_zero (sub_ne_zero.mpr hx.symm) hb0) hcurve.symm
  apply Or.inr
  rw [difference_x D x₁ y₁ x₂ y₂ hx h₁ h₂]
  apply slope_pole w hna x₁ x₂ _ hx₁ hx₂
  rw [alternative_slope D x₁ y₁ x₂ y₂ hx hy
    (FormalChartDouble.ordinate_equation D x₁ y₁ h₁)
    (FormalChartDouble.ordinate_equation D x₂ y₂ h₂),map_div₀,map_neg_eq_map]
  change 1<w b/w (y₂-y₁)
  rw [hb]
  exact (one_lt_div (w.pos (sub_ne_zero.mpr hy.symm))).mpr hdy

/-- The same-x inverse branch uses actual doubling, with the exact tangent
slope rather than an inapplicable secant division. -/
theorem tangent_formal (D x y : F) (hD : w D≤1)
    (h : (E D).Nonsingular x y) (hx : w x≤1) (hy : y≠0)
    (hs : w (2*y)<w (3*x^2-D)) :
    Point.some x y h+Point.some x y h∈
      AlgebraicFormalSubgroup318.formalSubgroup w hna D hD := by
  have hneg : y≠(E D).negY x y := by
    simp only [negY,E,zero_mul,sub_zero]
    intro he
    have hz : 2*y=0 := by linear_combination he
    exact mul_ne_zero (by norm_num) hy hz
  have hslope : (E D).slope x x y y=(3*x^2-D)/(2*y) := by
    rw [slope_of_Y_ne rfl hneg]
    simp only [E,zero_mul,add_zero,sub_zero,negY,sub_neg_eq_add]
    congr 1 <;> ring
  apply Or.inr
  rw [Point.add_self_of_Y_ne hneg]
  simp only [Point.xRep_some,Matrix.cons_val_zero]
  rw [addX,hslope]
  simp only [E,zero_mul,add_zero,sub_zero]
  apply slope_pole w hna x x _ hx hx
  rw [map_div₀]
  exact (one_lt_div (w.pos (mul_ne_zero (by norm_num) hy))).mpr hs

/-- All exact affine difference cases are retained: secants, equality, and
the same-x inverse/tangent branch. This is the local finite-code implication
needed to construct actual entry into the formal subgroup. -/
theorem close_points (D x₁ y₁ x₂ y₂ : F) (hD : w D≤1)
    (h₁ : (E D).Nonsingular x₁ y₁) (h₂ : (E D).Nonsingular x₂ y₂)
    (hx₁ : w x₁≤1) (hx₂ : w x₂≤1)
    (hc : (w (x₂-x₁)<w (2*y₁) ∧ w (y₂-y₁)<w (2*y₁)) ∨
      (w (x₂-x₁)<w (3*x₁^2-D) ∧ w (y₂-y₁)<w (3*x₁^2-D))) :
    Point.some x₁ y₁ h₁-Point.some x₂ y₂ h₂∈
      AlgebraicFormalSubgroup318.formalSubgroup w hna D hD := by
  by_cases hx : x₁=x₂
  · subst x₂
    have he : y₁^2=y₂^2 :=
      (FormalChartDouble.ordinate_equation D x₁ y₁ h₁).trans
        (FormalChartDouble.ordinate_equation D x₁ y₂ h₂).symm
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with hy|hy
    · subst y₂
      simp only [sub_self]
      exact AddSubgroup.zero_mem _
    · have hy' : y₂= -y₁ := by rw [hy,neg_neg]
      have hdy : w (y₂-y₁)=w (2*y₁) := by
        rw [hy',show -y₁-y₁= -(2*y₁) by ring,map_neg_eq_map]
      by_cases hz : y₁=0
      · have hz' : y₂=0 := by simpa only [hz,neg_zero] using hy'
        subst y₁
        subst y₂
        simp only [sub_self]
        exact AddSubgroup.zero_mem _
      · have hs : w (2*y₁)<w (3*x₁^2-D) := by
          rcases hc with h|h
          · rw [hdy] at h
            exact False.elim (lt_irrefl _ h.2)
          · simpa only [hdy] using h.2
        have hpoint : Point.some x₁ y₂ h₂= -Point.some x₁ y₁ h₁ := by
          rw [Point.neg_some,Point.some.injEq]
          exact ⟨rfl,by simpa only [negY,E,zero_mul,sub_zero] using hy'⟩
        rw [hpoint,sub_neg_eq_add]
        exact tangent_formal w hna D x₁ y₁ hD h₁ hx₁ hz hs
  · rcases hc with h|h
    · apply close_ordinate_secant w hna D x₁ y₁ x₂ y₂ hD h₁ h₂ hx hx₁ hx₂ _ h.2
      rw [show x₁-x₂= -(x₂-x₁) by ring,map_neg_eq_map]
      exact h.1
    · exact close_derivative_secant w hna D x₁ y₁ x₂ y₂ hD h₁ h₂ hx hx₁ hx₂ h.1 h.2

end LocalPointDifference318
