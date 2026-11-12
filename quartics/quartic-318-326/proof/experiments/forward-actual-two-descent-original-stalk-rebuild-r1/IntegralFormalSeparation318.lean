module
public import GoodReductionLifting318
public section
noncomputable section
namespace IntegralFormalSeparation318
open ReciprocalDouble318 WeierstrassCurve.Affine LocalDerivativeSeparation318 LocalPointDifference318
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]
variable (w : AbsoluteValue F ℝ) (hna : IsNonarchimedean w)

include hna in
lemma add_integral (x y : F) (hx : w x≤1) (hy : w y≤1) : w (x+y)≤1 :=
  (hna x y).trans (max_le hx hy)
include hna in
lemma sub_integral (x y : F) (hx : w x≤1) (hy : w y≤1) : w (x-y)≤1 := by
  simpa only [sub_eq_add_neg,map_neg_eq_map] using
    add_integral w hna x (-y) hx (by simpa only [map_neg_eq_map] using hy)
lemma mul_integral (x y : F) (hx : w x≤1) (hy : w y≤1) : w (x*y)≤1 := by
  rw [map_mul]
  exact mul_le_one₀ hx (apply_nonneg w y) hy
lemma pow_integral (x : F) (hx : w x≤1) (n : ℕ) : w (x^n)≤1 := by
  rw [map_pow]
  exact pow_le_one₀ (apply_nonneg w x) hx
include hna in
lemma slope_integral (x y m : F) (hx : w x≤1) (hy : w y≤1) (hm : w m≤1) :
    w (m^2-x-y)≤1 :=
  sub_integral w hna _ _ (sub_integral w hna _ _ (pow_integral w m hm 2) hx) hy
include hna in
lemma secant_coefficient_integral (D x y : F) (hD : w D≤1) (hx : w x≤1) (hy : w y≤1) :
    w (x^2+x*y+y^2-D)≤1 :=
  sub_integral w hna _ _
    (add_integral w hna _ _ (add_integral w hna _ _
      (pow_integral w x hx 2) (mul_integral w _ _ hx hy)) (pow_integral w y hy 2)) hD
include hna in
lemma tangent_coefficient_integral (D x : F) (hD : w D≤1) (hx : w x≤1) :
    w (3*x^2-D)≤1 :=
  sub_integral w hna _ _ (mul_integral w _ _ (nat_le_one w hna 3) (pow_integral w x hx 2)) hD

/-- Different integral residue coordinates force the actual secant or
tangent difference to remain integral. This is the converse direction
needed for an injective good-reduction code of the original formal quotient. -/
theorem separated_difference (D x₁ y₁ x₂ y₂ : F) (hD : w D≤1)
    (h₁ : (E D).Nonsingular x₁ y₁) (h₂ : (E D).Nonsingular x₂ y₂)
    (hx₁ : w x₁≤1) (hy₁ : w y₁≤1) (hx₂ : w x₂≤1) (hy₂ : w y₂≤1)
    (hsep : w (x₁-x₂)=1 ∨ w (y₂-y₁)=1) :
    Point.some x₁ y₁ h₁-Point.some x₂ y₂ h₂∉
      AlgebraicFormalSubgroup318.formalSubgroup w hna D hD := by
  have hne : Point.some x₁ y₁ h₁≠Point.some x₂ y₂ h₂ := by
    intro he
    have hh := Point.some.inj he
    rcases hsep with hs|hs
    · simpa only [hh.1,sub_self,map_zero] using hs
    · simpa only [hh.2,sub_self,map_zero] using hs
  have hb : w ((Point.some x₁ y₁ h₁-Point.some x₂ y₂ h₂).xRep 0)≤1 := by
    by_cases hx : x₁=x₂
    · subst x₂
      have hy : y₁≠y₂ := by intro he; subst y₂; exact hne rfl
      have hc : y₁^2=y₂^2 := (FormalChartDouble.ordinate_equation D x₁ y₁ h₁).trans
        (FormalChartDouble.ordinate_equation D x₁ y₂ h₂).symm
      have hminus : y₂= -y₁ := by
        have hh := (sq_eq_sq_iff_eq_or_eq_neg.mp hc).resolve_left hy
        rw [hh,neg_neg]
      have hunit : w (2*y₁)=1 := by
        rcases hsep with hs|hs
        · simpa only [sub_self,map_zero] using hs
        · simpa only [hminus,show -y₁-y₁= -(2*y₁) by ring,map_neg_eq_map] using hs
      have h2y : 2*y₁≠0 := AlgebraicFormalSubgroup318.ne_zero_of_unit w _ hunit
      have hyneg : y₁≠(E D).negY x₁ y₁ := by
        simp only [negY,E,zero_mul,sub_zero]
        intro he
        apply h2y
        linear_combination he
      have hpneg : Point.some x₁ y₂ h₂= -Point.some x₁ y₁ h₁ := by
        rw [Point.neg_some]
        congr 1
        simpa only [negY,E,zero_mul,sub_zero] using hminus
      rw [hpneg,sub_neg_eq_add,Point.add_self_of_Y_ne hyneg]
      simp only [Point.xRep_some,Matrix.cons_val_zero]
      have hslope : (E D).slope x₁ x₁ y₁ y₁=(3*x₁^2-D)/(2*y₁) := by
        rw [slope_of_Y_ne rfl hyneg]
        simp only [E,zero_mul,add_zero,sub_zero,negY,sub_neg_eq_add]
        congr 1 <;> ring
      rw [addX,hslope]
      simp only [E,zero_mul,add_zero,sub_zero]
      apply slope_integral w hna _ _ _ hx₁ hx₁
      rw [map_div₀,hunit,div_one]
      exact tangent_coefficient_integral w hna D x₁ hD hx₁
    · rw [difference_x D x₁ y₁ x₂ y₂ hx h₁ h₂]
      apply slope_integral w hna _ _ _ hx₁ hx₂
      rcases hsep with hs|hs
      · rw [map_div₀,hs,div_one]
        exact add_integral w hna _ _ hy₁ hy₂
      · have hy : y₁≠y₂ := by
          intro he
          simpa only [he,sub_self,map_zero] using hs
        rw [alternative_slope D x₁ y₁ x₂ y₂ hx hy
          (FormalChartDouble.ordinate_equation D x₁ y₁ h₁)
          (FormalChartDouble.ordinate_equation D x₂ y₂ h₂),map_div₀,map_neg_eq_map,hs,div_one]
        exact secant_coefficient_integral w hna D x₁ x₂ hD hx₁ hx₂
  intro hf
  rcases hf with hz|hpole
  · exact hne (sub_eq_zero.mp hz)
  · exact (not_lt_of_ge hb) hpole

end IntegralFormalSeparation318
