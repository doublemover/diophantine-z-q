module
public import ActualTwoDescentOriginalRootTranslations318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootAddition318
open ActualTwoDescentOriginalRootIdeals318 ActualTwoDescentOriginalRootTranslations318
open ActualTwoDescentEllipticModel318
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

lemma actual_root_secant (n x y : K) (i : Fin 3) (hd : rootWeight n x i ≠ 0) :
    (curve n).toAffine.slope x (root n i) y 0=y/rootWeight n x i := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (sub_ne_zero.mp hd)]
  simp only [rootWeight,sub_zero]

lemma actual_root_addX (n x y : K) (i : Fin 3) (hd : rootWeight n x i ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) :
    (curve n).toAffine.addX x (root n i) ((curve n).toAffine.slope x (root n i) y 0)=
      rootTranslateX n x i := by
  rw [actual_root_secant n x y i hd]
  simp only [WeierstrassCurve.Affine.addX,curve,zero_mul,add_zero]
  rw [div_pow,hc]
  fin_cases i
  all_goals
    simp [rootWeight,root] at hd
    simp only [rootWeight,root,rootTranslateX,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,sub_zero,sub_neg_eq_add]
    field_simp [hd] <;> ring

lemma actual_root_addY (n x y : K) (i : Fin 3) (hd : rootWeight n x i ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) :
    (curve n).toAffine.addY x (root n i) y ((curve n).toAffine.slope x (root n i) y 0)=
      rootTranslateY n x y i := by
  rw [WeierstrassCurve.Affine.addY,curve_negY,WeierstrassCurve.Affine.negAddY,
    actual_root_addX n x y i hd hc,actual_root_secant n x y i hd]
  fin_cases i
  all_goals
    simp [rootWeight,root] at hd
    simp only [rootWeight,root,rootTranslateX,rootTranslateY,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,sub_zero,sub_neg_eq_add]
    field_simp [hd] <;> ring

/-- ALL three formulas are identified with addition by the ACTUAL affine
root point in the original elliptic group, not merely a rational x-action. -/
theorem actual_root_translation_is_addition (n x y : K) (hn : n ≠ 0) (i : Fin 3)
    (hd : rootWeight n x i ≠ 0) (hc : y^2=x*(x-n)*(x+3*n)) :
    point n x y hn hc+rootPoint n hn i=
      point n (rootTranslateX n x i) (rootTranslateY n x y i) hn
        (actual_root_translation_curve n x y i hd hc) := by
  unfold rootPoint point
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (sub_ne_zero.mp hd)]
  congr 1
  · exact actual_root_addX n x y i hd hc
  · exact actual_root_addY n x y i hd hc

end ActualTwoDescentOriginalRootAddition318
