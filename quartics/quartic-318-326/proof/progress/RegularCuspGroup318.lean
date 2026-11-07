module
public import RegularCusp318
public section
namespace RegularCuspGroup318
open WeierstrassCurve.Affine ReciprocalDouble318 RegularCusp318
variable {F:Type*} [Field F] [CharZero F] [DecidableEq F]
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem curve_equation (D x y:F) (h:(E D).Nonsingular x y) : y^2=x^3-D*x := by
  simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using h.1

theorem actual_addX_regular (w:AbsoluteValue F ℝ) (hna:IsNonarchimedean (w ·))
    (D x₁ y₁ x₂ y₂:F) (hD:w D<1) (h2:w (2:F)≤1)
    (h₁:(E D).Nonsingular x₁ y₁) (h₂:(E D).Nonsingular x₂ y₂)
    (hx₁:1≤w x₁) (hx₂:1≤w x₂)
    (hxy:¬(x₁=x₂ ∧ y₁=(E D).negY x₂ y₂)) :
    1≤w ((E D).addX x₁ x₂ ((E D).slope x₁ x₂ y₁ y₂)) := by
  let l:=(E D).slope x₁ x₂ y₁ y₂
  have hc₁:=curve_equation D x₁ y₁ h₁
  have hc₂:=curve_equation D x₂ y₂ h₂
  have hsl : l*(x₁-x₂)=y₁-y₂ ∧ l*(y₁+y₂)=x₁^2+x₁*x₂+x₂^2-D := by
    by_cases hx:x₁=x₂
    · have hy:y₁≠(E D).negY x₂ y₂ := fun hh=>hxy ⟨hx,hh⟩
      have he:=Y_eq_of_Y_ne h₁.1 h₂.1 hx hy
      subst x₂
      subst y₂
      constructor
      · simp
      · have hy0:y₁≠0 := by
          intro hz
          apply hy
          simp [hz,negY,E]
        dsimp [l]
        rw [slope_of_Y_ne rfl hy]
        simp only [E,zero_mul,mul_zero,add_zero,sub_zero,negY,sub_neg_eq_add]
        field_simp [hy0]
        ring
    · have hl:l*(x₁-x₂)=y₁-y₂ := by
        dsimp [l]
        rw [slope_of_X_ne hx]
        exact div_mul_cancel₀ _ (sub_ne_zero.mpr hx)
      exact ⟨hl,secant_slope_sym D x₁ y₁ x₂ y₂ l hc₁ hc₂ hx hl⟩
  obtain ⟨hs,hp,hm⟩:=slope_vieta D x₁ y₁ x₂ y₂ l hc₁ hsl.1 hsl.2
  have hh:=third_regular w hna D x₁ x₂ (l^2-x₁-x₂) l (y₁-l*x₁) hD h2 hx₁ hx₂ hs hp hm
  simpa only [addX,E,zero_mul,add_zero,sub_zero,l] using hh

/-- The actual regular locus at every cusp place is an additive subgroup. -/
@[expose] def regularSubgroup (w:AbsoluteValue F ℝ) (hna:IsNonarchimedean (w ·))
    (D:F) (hD:w D<1) (h2:w (2:F)≤1) : AddSubgroup (E D).Point where
  carrier := {Q | 1≤w (Q.xRep 0)}
  zero_mem' := by simp [Point.xRep_zero]
  neg_mem' := by
    intro Q hQ
    change 1≤w ((-Q).xRep 0)
    change 1≤w (Q.xRep 0) at hQ
    simpa only [Point.xRep_neg] using hQ
  add_mem' := by
    intro P Q hP hQ
    change 1≤w (P.xRep 0) at hP
    change 1≤w (Q.xRep 0) at hQ
    cases P with
    | zero =>
      change 1≤w (((0:(E D).Point)+Q).xRep 0)
      simpa only [zero_add] using hQ
    | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
        change 1≤w ((Point.some x₁ y₁ h₁+(0:(E D).Point)).xRep 0)
        simpa only [add_zero] using hP
      | some x₂ y₂ h₂ =>
        change 1≤w ((Point.some x₁ y₁ h₁+Point.some x₂ y₂ h₂).xRep 0)
        by_cases hxy:x₁=x₂ ∧ y₁=(E D).negY x₂ y₂
        · rw [Point.add_of_Y_eq hxy.1 hxy.2]
          simp [Point.xRep_zero]
        · rw [Point.add_some hxy]
          change 1≤w ((E D).addX x₁ x₂ ((E D).slope x₁ x₂ y₁ y₂))
          exact actual_addX_regular w hna D x₁ y₁ x₂ y₂ hD h2 h₁ h₂ hP hQ hxy

theorem multiple_regular (w:AbsoluteValue F ℝ) (hna:IsNonarchimedean (w ·))
    (D:F) (hD:w D<1) (h2:w (2:F)≤1) (P:(E D).Point)
    (hP:1≤w (P.xRep 0)) (n:ℤ) : 1≤w ((n • P).xRep 0) :=
  (regularSubgroup w hna D hD h2).zsmul_mem hP n

end
end RegularCuspGroup318
#print axioms RegularCuspGroup318.regularSubgroup
#print axioms RegularCuspGroup318.multiple_regular
