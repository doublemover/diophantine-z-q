module
public import OriginalCasselsLiteralIsogenyExceptional318
public import OriginalCasselsAffineChordImage318
import all OriginalCasselsAffineChordImage318
public import ActualTwoDescentChordPolynomial318
import all OriginalSelectedCasselsParity318
import all ActualTwoDescentEllipticModel318
import all OriginalCasselsLiteralIsogenyPoint318
public section

noncomputable section

namespace OriginalCasselsLiteralIsogenySecant318

open ActualTwoDescentEllipticModel318 ActualTwoDescentChordPolynomial318
open OriginalSelectedCasselsParity318 OriginalCasselsLiteralIsogenyPoint318
open OriginalCasselsLiteralIsogenyExceptional318 OriginalCasselsAffineChordImage318
open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

abbrev Ximage (n x : F) : F := x+2*n-3*n^2/x
abbrev Yimage (n x y : F) : F := y+3*n^2*y/x^2
abbrev imageSlope (n m c : F) : F := m+3*n^2/c
abbrev imageIntercept (n m c : F) : F := c-2*n*m-3*n^2*m^2/c

theorem source_x (n x₁ x₂ m : F) :
    (curve n).toAffine.addX x₁ x₂ m = m^2-2*n-x₁-x₂ := by
  simp [addX,curve]

theorem source_y (n x₁ x₂ y₁ m : F) :
    (curve n).toAffine.addY x₁ x₂ y₁ m =
      -(m*((curve n).toAffine.addX x₁ x₂ m-x₁)+y₁) := by
  rw [addY,curve_negY,negAddY]

theorem target_x (n x₁ x₂ m : F) :
    (targetModel n).toAffine.addX x₁ x₂ m = m^2+4*n-x₁-x₂ := by
  simp [addX,targetModel,sub_neg_eq_add]

theorem target_y (n x₁ x₂ y₁ m : F) :
    (targetModel n).toAffine.addY x₁ x₂ y₁ m =
      -(m*((targetModel n).toAffine.addX x₁ x₂ m-x₁)+y₁) := by
  rw [addY,target_negY,negAddY]

theorem cut_of_equation (n m c x y : F) (he : y^2=x*(x-n)*(x+3*n))
    (hy : y=m*x+c) : cut n m c x = 0 := by
  dsimp [cut]
  rw [hy] at he
  linear_combination -he

/-- Actual affine sum, with the sign on the third intersection built into
the output label; this also applies to an actual source tangent. -/
theorem source_sum (n x₁ y₁ x₂ y₂ m x₃ c : F) (hn : n ≠ 0)
    (he₁ : y₁^2=x₁*(x₁-n)*(x₁+3*n)) (he₂ : y₂^2=x₂*(x₂-n)*(x₂+3*n))
    (hnv : ¬(x₁=x₂ ∧ y₁=(curve n).toAffine.negY x₂ y₂))
    (hm : (curve n).toAffine.slope x₁ x₂ y₁ y₂=m)
    (hx₃ : x₃=m^2-2*n-x₁-x₂) (hc : c=y₁-m*x₁) :
    ∃ he₃ : (m*x₃+c)^2=x₃*(x₃-n)*(x₃+3*n),
      point n x₁ y₁ hn he₁ + point n x₂ y₂ hn he₂ =
        -point n x₃ (m*x₃+c) hn he₃ := by
  have hX : (curve n).toAffine.addX x₁ x₂ m=x₃ := (source_x n x₁ x₂ m).trans hx₃.symm
  have hY : (curve n).toAffine.negAddY x₁ x₂ y₁ m=m*x₃+c := by
    rw [negAddY,hX,hc]
    ring
  have h := equation_negAdd ((curve_equation n x₁ y₁).mpr he₁)
    ((curve_equation n x₂ y₂).mpr he₂) hnv
  rw [hm,hX,hY] at h
  refine ⟨(curve_equation n _ _).mp h,?_⟩
  unfold point
  rw [Point.add_some hnv,Point.neg_some,Point.some.injEq]
  constructor
  · rw [hm,hX]
  · rw [hm,source_y,hX,curve_negY,hc] <;> ring

private theorem source_vieta (n x₁ y₁ x₂ y₂ m x₃ c : F)
    (he₁ : y₁^2=x₁*(x₁-n)*(x₁+3*n)) (he₂ : y₂^2=x₂*(x₂-n)*(x₂+3*n))
    (hnv : ¬(x₁=x₂ ∧ y₁=(curve n).toAffine.negY x₂ y₂))
    (hm : (curve n).toAffine.slope x₁ x₂ y₁ y₂=m)
    (hx₃ : x₃=m^2-2*n-x₁-x₂) (hc : c=y₁-m*x₁) :
    x₁*x₂+x₁*x₃+x₂*x₃= -3*n^2-2*m*c ∧ x₁*x₂*x₃=c^2 := by
  have h := actual_chord_polynomial n x₁ y₁ x₂ y₂
    ((curve_equation n x₁ y₁).mpr he₁) ((curve_equation n x₂ y₂).mpr he₂) hnv
  change cubicPolynomial n-(chordLine x₁ y₁ ((curve n).toAffine.slope x₁ x₂ y₁ y₂))^2=
    (Polynomial.X-Polynomial.C x₁)*(Polynomial.X-Polynomial.C x₂)*
      (Polynomial.X-Polynomial.C ((curve n).toAffine.addX x₁ x₂
        ((curve n).toAffine.slope x₁ x₂ y₁ y₂))) at h
  rw [hm,source_x,←hx₃] at h
  have hd := actual_chord_derivative n x₁ y₁ m x₁ x₂ x₃ 0 h
  have hv := actual_chord_value n x₁ y₁ m x₁ x₂ x₃ 0 h (by simp)
  constructor
  · rw [hc]
    linear_combination -hd
  · simp only [sub_zero] at hv
    -- Normalize the retained definition of the intercept simultaneously.
    rw [hc]
    linear_combination hv

theorem actual_add_of_zero_intercept (n x₁ y₁ x₂ y₂ m x₃ : F) (hn : n ≠ 0)
    (he₁ : y₁^2=x₁*(x₁-n)*(x₁+3*n)) (he₂ : y₂^2=x₂*(x₂-n)*(x₂+3*n))
    (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0)
    (hnv : ¬(x₁=x₂ ∧ y₁=(curve n).toAffine.negY x₂ y₂))
    (hm : (curve n).toAffine.slope x₁ x₂ y₁ y₂=m)
    (hx₃ : x₃=m^2-2*n-x₁-x₂) (hc : 0=y₁-m*x₁) :
    literalMap n hn (point n x₁ y₁ hn he₁+point n x₂ y₂ hn he₂)=
      literalMap n hn (point n x₁ y₁ hn he₁)+literalMap n hn (point n x₂ y₂ hn he₂) := by
  obtain ⟨_,hp⟩ := source_vieta n x₁ y₁ x₂ y₂ m x₃ 0 he₁ he₂ hnv hm hx₃ hc
  have h₃ : x₃=0 := by
    apply (mul_eq_zero.mp (show (x₁*x₂)*x₃=0 by simpa using hp)).resolve_left
    exact mul_ne_zero h₁ h₂
  obtain ⟨he₃,hS⟩ := source_sum n x₁ y₁ x₂ y₂ m x₃ 0 hn he₁ he₂ hnv hm hx₃ hc
  apply actual_add_sum_kernel
  rw [hS]
  have hPt : point n x₃ (m*x₃+0) hn he₃ = kernelPoint n hn := by
    unfold kernelPoint point
    rw [Point.some.injEq]
    exact ⟨h₃,by rw [h₃,mul_zero,add_zero]⟩
  rw [hPt]
  calc
    -kernelPoint n hn = -kernelPoint n hn+(kernelPoint n hn+kernelPoint n hn) := by
      rw [OriginalCasselsLiteralKernelTranslation318.actual_kernel_double,add_zero]
    _ = kernelPoint n hn := by rw [←add_assoc,neg_add_cancel,zero_add]

/-- Single affine comparison for either a secant or a tangent, once the
literal target chord slope and the nonvertical branch are identified. -/
theorem actual_add_of_image_slope (n x₁ y₁ x₂ y₂ m x₃ c : F) (hn : n ≠ 0)
    (he₁ : y₁^2=x₁*(x₁-n)*(x₁+3*n)) (he₂ : y₂^2=x₂*(x₂-n)*(x₂+3*n))
    (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0) (hc₀ : c ≠ 0)
    (hnv : ¬(x₁=x₂ ∧ y₁=(curve n).toAffine.negY x₂ y₂))
    (hm : (curve n).toAffine.slope x₁ x₂ y₁ y₂=m)
    (hx₃ : x₃=m^2-2*n-x₁-x₂) (hc : c=y₁-m*x₁)
    (hNV : ¬(Ximage n x₁=Ximage n x₂ ∧
      Yimage n x₁ y₁=(targetModel n).toAffine.negY (Ximage n x₂) (Yimage n x₂ y₂)))
    (hM : (targetModel n).toAffine.slope (Ximage n x₁) (Ximage n x₂)
      (Yimage n x₁ y₁) (Yimage n x₂ y₂)=imageSlope n m c) :
    literalMap n hn (point n x₁ y₁ hn he₁+point n x₂ y₂ hn he₂)=
      literalMap n hn (point n x₁ y₁ hn he₁)+literalMap n hn (point n x₂ y₂ hn he₂) := by
  obtain ⟨hpair,hprod⟩ := source_vieta n x₁ y₁ x₂ y₂ m x₃ c he₁ he₂ hnv hm hx₃ hc
  have h₃ : x₃ ≠ 0 := by
    intro h
    have hh : c^2=0 := by simpa only [h,mul_zero] using hprod.symm
    exact pow_ne_zero 2 hc₀ hh
  have hsum : x₁+x₂+x₃=m^2-2*n := by rw [hx₃]; ring
  have hV := transformed_vieta n m c x₁ x₂ x₃ hc₀ h₁ h₂ h₃ hsum hpair hprod
  have hline₁ : y₁=m*x₁+c := by rw [hc]; ring
  obtain ⟨he₃,hS⟩ := source_sum n x₁ y₁ x₂ y₂ m x₃ c hn he₁ he₂ hnv hm hx₃ hc
  have hL₁ : Yimage n x₁ y₁=imageSlope n m c*Ximage n x₁+imageIntercept n m c := by
    rw [hline₁]
    exact oriented_image_line n m c x₁ hc₀ h₁ (cut_of_equation n m c x₁ y₁ he₁ hline₁)
  have hL₃ : Yimage n x₃ (m*x₃+c)=imageSlope n m c*Ximage n x₃+imageIntercept n m c :=
    oriented_image_line n m c x₃ hc₀ h₃ (cut_of_equation n m c x₃ _ he₃ rfl)
  rw [hS,actual_literal_neg,literal_affine n hn x₃ _ h₃,
    literal_affine n hn x₁ y₁ h₁,literal_affine n hn x₂ y₂ h₂]
  unfold imagePoint targetPoint
  rw [Point.add_some hNV,Point.neg_some,Point.some.injEq]
  have hX : (targetModel n).toAffine.addX (Ximage n x₁) (Ximage n x₂)
      (imageSlope n m c) = Ximage n x₃ := by
    rw [target_x]
    change _ = Ximage n x₃
    linear_combination -hV
  refine ⟨by rw [hM,hX],?_⟩
  rw [target_negY,hM,target_y,hX]
  change -Yimage n x₃ (m*x₃+c) =
    -(imageSlope n m c*(Ximage n x₃-Ximage n x₁)+Yimage n x₁ y₁)
  rw [hL₃,hL₁]
  ring

/-- True ordinary secant. The explicit target-distinctness premise is
not silently inferred from source distinctness. -/
theorem actual_add_distinct_nonkernel
    (n x₁ y₁ x₂ y₂ : F) (hn : n ≠ 0)
    (he₁ : y₁^2=x₁*(x₁-n)*(x₁+3*n)) (he₂ : y₂^2=x₂*(x₂-n)*(x₂+3*n))
    (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0) (hd : x₁ ≠ x₂)
    (hD : Ximage n x₁ ≠ Ximage n x₂) :
    literalMap n hn (point n x₁ y₁ hn he₁+point n x₂ y₂ hn he₂)=
      literalMap n hn (point n x₁ y₁ hn he₁)+literalMap n hn (point n x₂ y₂ hn he₂) := by
  let m := (y₁-y₂)/(x₁-x₂)
  let c := y₁-m*x₁
  let x₃ := m^2-2*n-x₁-x₂
  have hm : (curve n).toAffine.slope x₁ x₂ y₁ y₂=m := slope_of_X_ne hd
  have hnv : ¬(x₁=x₂ ∧ y₁=(curve n).toAffine.negY x₂ y₂) := fun h => hd h.1
  by_cases hc₀ : c=0
  · exact actual_add_of_zero_intercept n x₁ y₁ x₂ y₂ m x₃ hn he₁ he₂ h₁ h₂
      hnv hm rfl (hc₀.symm.trans (show c=y₁-m*x₁ from rfl))
  · have hl₁ : y₁=m*x₁+c := by dsimp [c]; ring
    have hl₂ : y₂=m*x₂+c := by
      dsimp [c,m]
      field_simp [sub_ne_zero.mpr hd] <;> ring
    have hL₁ : Yimage n x₁ y₁=imageSlope n m c*Ximage n x₁+imageIntercept n m c := by
      rw [hl₁]
      exact oriented_image_line n m c x₁ hc₀ h₁ (cut_of_equation n m c x₁ y₁ he₁ hl₁)
    have hL₂ : Yimage n x₂ y₂=imageSlope n m c*Ximage n x₂+imageIntercept n m c := by
      rw [hl₂]
      exact oriented_image_line n m c x₂ hc₀ h₂ (cut_of_equation n m c x₂ y₂ he₂ hl₂)
    apply actual_add_of_image_slope n x₁ y₁ x₂ y₂ m x₃ c hn he₁ he₂ h₁ h₂ hc₀
      hnv hm rfl rfl (fun h => hD h.1)
    rw [slope_of_X_ne hD,hL₁,hL₂]
    apply (div_eq_iff (sub_ne_zero.mpr hD)).2
    ring

end OriginalCasselsLiteralIsogenySecant318

#print axioms OriginalCasselsLiteralIsogenySecant318.actual_add_distinct_nonkernel
