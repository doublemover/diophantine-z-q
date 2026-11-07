module
public import GlobalFirstDescent318
public section
namespace ActualChord318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
noncomputable section

/-- The two elementary chord identities for the actual short curve. -/
theorem chord_identities (x₁ x₂ y₁ y₂ m b:K) (hx:x₁≠x₂)
    (h₁:y₁^2=x₁^3-D*x₁) (h₂:y₂^2=x₂^3-D*x₂)
    (hl₁:y₁=m*x₁+b) (hl₂:y₂=m*x₂+b) :
    x₁*x₂*(m^2-x₁-x₂)=b^2 ∧
    x₁*x₂+x₁*(m^2-x₁-x₂)+x₂*(m^2-x₁-x₂)= -D-2*m*b := by
  rw [hl₁] at h₁
  rw [hl₂] at h₂
  have hm:(x₁-x₂)*(x₁^2+x₁*x₂+x₂^2-m^2*(x₁+x₂)-D-2*m*b)=0 := by
    linear_combination -h₁+h₂
  have hq:x₁^2+x₁*x₂+x₂^2-m^2*(x₁+x₂)-D-2*m*b=0 :=
    (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hx)
  constructor
  · linear_combination -h₁-x₁*hq
  · linear_combination -hq

theorem square_ne_neg_D (s:K) : s^2≠ -D := by
  intro hs
  let r:ℝ:=Real.sqrt 2
  have hr:r^2=2:=Real.sq_sqrt (by norm_num)
  have he:=congrArg (FiniteScale318.realPlace r hr) hs
  simp only [map_pow,map_neg] at he
  have hd:=FiniteScale318.D_real_gt_one r hr
  nlinarith [sq_nonneg (FiniteScale318.realPlace r hr s)]

/-- A secant joining abscissas whose product is a nonzero square meets the
curve at a nonzero square abscissa. The zero-abscissa branch is excluded
by the actual real sign of D. -/
theorem secant_square_abscissa (x₁ x₂ y₁ y₂ s:K) (hx:x₁≠x₂) (hs:s≠0)
    (hprod:x₁*x₂=s^2) (h₁:E.Nonsingular x₁ y₁) (h₂:E.Nonsingular x₂ y₂) :
    ∃r:K,r≠0 ∧ E.addX x₁ x₂ (E.slope x₁ x₂ y₁ y₂)=r^2 := by
  let m:=E.slope x₁ x₂ y₁ y₂
  let b:=y₁-m*x₁
  have hm:m=(y₁-y₂)/(x₁-x₂) := by dsimp [m]; rw [slope_of_X_ne hx]
  have hl₁:y₁=m*x₁+b := by dsimp [b]; ring
  have hl₂:y₂=m*x₂+b := by
    dsimp [b]
    rw [hm]
    field_simp [sub_ne_zero.mpr hx]
    ring
  have he₁:y₁^2=x₁^3-D*x₁ := by
    have hh:=h₁.1; rw [equation_iff] at hh; simpa [E,sub_eq_add_neg] using hh
  have he₂:y₂^2=x₂^3-D*x₂ := by
    have hh:=h₂.1; rw [equation_iff] at hh; simpa [E,sub_eq_add_neg] using hh
  obtain ⟨hch,hco⟩:=chord_identities x₁ x₂ y₁ y₂ m b hx he₁ he₂ hl₁ hl₂
  have hb:b≠0 := by
    intro hz
    rw [hz,zero_pow (by decide),hprod] at hch
    have hz₃:m^2-x₁-x₂=0 := (mul_eq_zero.mp hch).resolve_left (pow_ne_zero _ hs)
    rw [hz₃,hz,hprod] at hco
    simp only [mul_zero,add_zero] at hco
    exact square_ne_neg_D s (by linear_combination hco)
  refine ⟨b/s,div_ne_zero hb hs,?_⟩
  change E.addX x₁ x₂ m=(b/s)^2
  rw [addX]
  simp only [E,zero_mul,add_zero,sub_zero]
  rw [div_pow]
  apply (eq_div_iff (pow_ne_zero 2 hs)).mpr
  rw [←hprod]
  linear_combination hch

/-- Equal nonzero x-squareclasses give an actual double, including the
same-abscissa tangent and inverse branches. -/
theorem square_product_sum_double (x₁ x₂ y₁ y₂ s:K) (hs:s≠0)
    (hprod:x₁*x₂=s^2) (h₁:E.Nonsingular x₁ y₁) (h₂:E.Nonsingular x₂ y₂) :
    ∃Q:E.Point,Q+Q=Point.some x₁ y₁ h₁+Point.some x₂ y₂ h₂ := by
  by_cases hx:x₁=x₂
  · rcases Point.X_eq_iff.mp hx with hh|hh
    · exact ⟨Point.some x₂ y₂ h₂,by rw [hh]⟩
    · exact ⟨0,by rw [hh,neg_add_cancel,add_zero]⟩
  · obtain ⟨r,hr,hx3⟩:=secant_square_abscissa x₁ x₂ y₁ y₂ s hx hs hprod h₁ h₂
    let y3:=E.addY x₁ x₂ y₁ (E.slope x₁ x₂ y₁ y₂)
    have hn:E.Nonsingular (r^2) y3 := by
      have hh:=nonsingular_add h₁ h₂ (fun hh=>hx hh.1)
      simpa only [hx3] using hh
    obtain ⟨j,hj,hjy⟩:=RootPointAlgebra318.factor_of_square_point r y3 hr hn
    obtain ⟨Q,hQ⟩:=GlobalDualSquare318.square_halving r j hj
    refine ⟨Q,?_⟩
    rw [Point.add_of_X_ne hx]
    simpa only [hx3,hjy] using hQ

theorem square_product_difference_double (x₁ x₂ y₁ y₂ s:K) (hs:s≠0)
    (hprod:x₁*x₂=s^2) (h₁:E.Nonsingular x₁ y₁) (h₂:E.Nonsingular x₂ y₂) :
    ∃Q:E.Point,Q+Q=Point.some x₁ y₁ h₁-Point.some x₂ y₂ h₂ := by
  have hn:E.Nonsingular x₂ (E.negY x₂ y₂):=(nonsingular_neg ..).mpr h₂
  simpa only [sub_eq_add_neg,Point.neg_some] using
    square_product_sum_double x₁ x₂ y₁ (E.negY x₂ y₂) s hs hprod h₁ hn

end
end ActualChord318
#print axioms ActualChord318.secant_square_abscissa
