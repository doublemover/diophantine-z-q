module
public import ActualTwoDescentActualTorsionPoint318
public section
noncomputable section
namespace ActualTwoDescentTranslationGroupLaw318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentActualTorsionPoint318
open ActualTwoDescentTorsionTranslation318
variable [DecidableEq K]

lemma actual_torsion_secant (n x y : K) (hA : x+3*n ≠ 0) :
    (curve n).toAffine.slope x (-3*n) y 0=y/(x+3*n) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (by intro he; apply hA; rw [he]; ring)]
  congr 1 <;> ring

lemma actual_translation_addX (n x y : K) (hA : x+3*n ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) :
    (curve n).toAffine.addX x (-3*n) ((curve n).toAffine.slope x (-3*n) y 0)=translatedX n x := by
  rw [actual_torsion_secant n x y hA]
  dsimp [WeierstrassCurve.Affine.addX,curve]
  calc
    (y/(x+3*n))^2+0*(y/(x+3*n))-2*n-x-(-3*n)=
        (y^2+(n-x)*(x+3*n)^2)/(x+3*n)^2 := by field_simp [hA]; ring
    _=translatedX n x := by
      rw [hc]
      dsimp [translatedX]
      field_simp [hA]
      <;> ring

lemma actual_translation_addY (n x y : K) (hA : x+3*n ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) :
    (curve n).toAffine.addY x (-3*n) y ((curve n).toAffine.slope x (-3*n) y 0)=translatedY n x y := by
  rw [WeierstrassCurve.Affine.addY,curve_negY,WeierstrassCurve.Affine.negAddY,
    actual_translation_addX n x y hA hc,actual_torsion_secant n x y hA]
  dsimp [translatedX,translatedY]
  field_simp [hA]
  <;> ring

/-- The earlier rational involution is EXACTLY addition by the retained
nonzero two-torsion point in the actual elliptic group. -/
theorem actual_translation_is_addition (n x y : K) (hn : n ≠ 0) (hA : x+3*n ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) :
    point n x y hn hc+torsionPoint n hn =
      point n (translatedX n x) (translatedY n x y) hn (translated_curve n x y hA hc) := by
  unfold point torsionPoint
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by intro he; apply hA; rw [he]; ring)]
  congr 1
  · exact actual_translation_addX n x y hA hc
  · exact actual_translation_addY n x y hA hc

end ActualTwoDescentTranslationGroupLaw318
