module
public import SelectedCountDenominatorFactors318
public section
noncomputable section
namespace GlobalDoubleCoordinateCertificate318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
local instance : DecidableEq K := Classical.decEq _
lemma not_negative (x y : K) (hy : y≠0) : y≠E.negY x y := by
  simp only [negY,E,zero_mul,sub_zero]
  intro he
  have hh : 2*y=0 := by linear_combination he
  exact (mul_ne_zero (by norm_num) hy) hh
/-- A multiplication certificate avoids trusting numerical evaluation of
the elliptic group law. The denominator is certified nonzero. -/
lemma slope (x y m : K) (hy : y≠0) (hm : m*(2*y)=3*x^2-D) :
    E.slope x x y y=m := by
  rw [slope_of_Y_ne' (not_negative x y hy)]
  simp only [E,mul_zero,zero_mul,add_zero,sub_zero,sub_neg_eq_add]
  apply (div_eq_iff (show y+y≠0 by simpa [two_mul] using
    mul_ne_zero (show (2:K)≠0 by norm_num) hy)).mpr
  simpa only [two_mul,sub_eq_add_neg] using hm.symm
lemma double (x y m X Y : K) (hn : E.Nonsingular x y) (hy : y≠0)
    (hm : m*(2*y)=3*x^2-D) (hx : m^2-x-x=X)
    (hy' : m*(x-X)-y=Y) :
    ∃ h : E.Nonsingular X Y, Point.some x y hn+Point.some x y hn=Point.some X Y h := by
  have hny:=not_negative x y hy
  have hs:=slope x y m hy hm
  have hX : E.addX x x (E.slope x x y y)=X := by
    rw [hs,addX]
    simpa only [E,zero_mul,add_zero,sub_zero] using hx
  have hY : E.addY x x y (E.slope x x y y)=Y := by
    rw [addY,negAddY,negY,hX,hs]
    simp only [E,zero_mul,sub_zero]
    linear_combination hy'
  have hns:=nonsingular_add hn hn (fun he => hny he.2)
  have hns' : E.Nonsingular X Y := by simpa only [hX,hY] using hns
  refine ⟨hns',?_⟩
  rw [Point.add_self_of_Y_ne hny]
  simp only [hX,hY]
lemma double_x (x y m X : K) (hn : E.Nonsingular x y) (hy : y≠0)
    (hm : m*(2*y)=3*x^2-D) (hx : m^2-x-x=X) :
    (Point.some x y hn+Point.some x y hn).xRep 0=X := by
  have hny:=not_negative x y hy
  rw [Point.add_self_of_Y_ne hny,Point.xRep_some,Matrix.cons_val_zero]
  rw [slope x y m hy hm,addX]
  simpa only [E,zero_mul,add_zero,sub_zero] using hx
end GlobalDoubleCoordinateCertificate318
