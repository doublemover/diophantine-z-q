module
public import ActualLSGUnitSquarePeriod318
public import ActualVendorLSGWeierstrassDictionary318
public import ActualGaussianWeberShortScale318
public import ActualGaussianWeberQuarterTurn318
public section
noncomputable section

namespace ActualLSGOriginalPositiveIScale318

open Complex WeierstrassCurve WeierstrassCurve.Affine
open LSG.Weierstrass LSG.LemniscateIndep
open ActualLSGUnitSquarePeriod318
open ActualGaussianWeberShortScale318 ActualGaussianWeberQuarterTurn318
open ActualGaussianWeberHenselianPointMap318

attribute [local instance] Classical.decEq

private theorem one_div_I_cube : (1:ℂ)/Complex.I^3=Complex.I := by
  have h3 : Complex.I^3= -Complex.I := by
    calc
      _ = Complex.I^2*Complex.I := by ring
      _ = _ := by rw [Complex.I_sq,neg_one_mul]
  apply (div_eq_iff (pow_ne_zero 3 Complex.I_ne_zero)).2
  rw [h3]
  calc
    (1:ℂ) = -(Complex.I^2) := by rw [Complex.I_sq,neg_neg]
    _ = _ := by ring

private theorem rotate_cube (z w : ℂ) :
    (2:ℂ)/(Complex.I*z-Complex.I*w)^3 = Complex.I*(2/(z-w)^3) := by
  calc
    _ = ((1:ℂ)*2)/(Complex.I^3*(z-w)^3) := by rw [←mul_sub,mul_pow,one_mul]
    _ = (1/Complex.I^3)*(2/(z-w)^3) := mul_div_mul_comm _ _ _ _
    _ = _ := by rw [one_div_I_cube]

/-- The positive imaginary quarter-turn of the ordinate is a lattice
sum identity, including the totalized values at lattice points. -/
private theorem wpPrime_I (L : PeriodPair) {a : ℝ}
    (h₁ : L.ω₁=a) (h₂ : L.ω₂=Complex.I*a) (z : ℂ) :
    L.derivWeierstrassP (Complex.I*z)=Complex.I*L.derivWeierstrassP z := by
  have h := tsum_mulI h₁ h₂ (fun w : ℂ => 2/(Complex.I*z-w)^3)
  simp only [PeriodPair.derivWeierstrassP]
  rw [←h]
  simp only [rotate_cube,tsum_mul_left,mul_neg]

private abbrev s : ℂ := (fourthScale:ℂ)
private theorem s_ne : s≠0 := by exact_mod_cast fourthScale_pos.ne'
private theorem twoC : (2:ℂ)≠0 := by norm_num

private theorem actual_model : LSG.Weierstrass.curve L=short (s^4) := by
  unfold LSG.Weierstrass.curve short
  simp only [neg_div,←scale_matches,g3_zero,neg_zero,zero_div]

private def changeCurve {C D : WeierstrassCurve ℂ} (e : C=D) :
    C.toAffine.Point≃+D.toAffine.Point := e ▸ AddEquiv.refl _

private theorem change_some {C D : WeierstrassCurve ℂ} (e : C=D)
    {x y : ℂ} (h : C.toAffine.Nonsingular x y) :
    changeCurve e (Point.some x y h)=Point.some x y (e ▸ h) := by
  subst D
  rfl

private def comparison : (LSG.Weierstrass.curveA L).Point≃+WP ℂ :=
  (changeCurve actual_model).trans (normalizeEquiv twoC s_ne)

private theorem comparison_some {x y : ℂ} (h : (LSG.Weierstrass.curveA L).Nonsingular x y) :
    comparison (Point.some x y h)=Point.some (x/s^2) (y/s^3)
      (normalized_nonsing twoC s_ne (actual_model ▸ h)) := by
  unfold comparison
  rw [AddEquiv.trans_apply,change_some,normalizeEquiv_apply,normalize_some]

/-- The actual stock exponential on the unit-square lattice, normalized
to the original curve by the strictly positive real coordinate scale. -/
def expOriginal : ℂ →+ WP ℂ := comparison.toAddMonoidHom.comp (LSG.Weierstrass.expHom L)

private theorem exp_apply (z : ℂ) :
    expOriginal z=comparison (LSG.Weierstrass.expE L z) := by
  unfold expOriginal
  rw [AddMonoidHom.comp_apply,LSG.Weierstrass.expHom_apply] <;> rfl

private theorem not_lattice_I {z : ℂ} (h : z∉L.lattice) : Complex.I*z∉L.lattice := by
  intro hi
  have h' := I_mul_mem period_one period_i hi
  rw [←mul_assoc,Complex.I_mul_I,neg_one_mul] at h'
  exact h (by simpa only [neg_neg] using L.lattice.neg_mem h')

/-- Positive imaginary rotation on the actual original point model. -/
theorem exp_I (z : ℂ) : expOriginal (Complex.I*z)=turn twoC Complex.I Complex.I_sq (expOriginal z) := by
  simp only [exp_apply]
  by_cases h : z∈L.lattice
  · rw [LSG.Weierstrass.expE_of_mem L h,
      LSG.Weierstrass.expE_of_mem L (I_mul_mem period_one period_i h),comparison.map_zero] <;> rfl
  · rw [LSG.Weierstrass.expE_of_notMem L h,
      LSG.Weierstrass.expE_of_notMem L (not_lattice_I h),comparison_some,comparison_some,turn_some]
    apply some_transport
    · rw [weierstrassP_I_mul period_one period_i,neg_div]
    · rw [wpPrime_I L period_one period_i,mul_div_assoc] <;> ring

end ActualLSGOriginalPositiveIScale318
