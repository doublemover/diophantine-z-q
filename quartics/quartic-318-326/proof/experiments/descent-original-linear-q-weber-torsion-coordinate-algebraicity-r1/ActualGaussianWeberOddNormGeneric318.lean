module
public import ActualGaussianWeberTranslationFunctionField318
public import ActualGaussianWeberStockCoordinateHom318
public import ActualGaussianWeberGaussianScalarCore318
public import Mathlib.Data.ZMod.Basic
public section
noncomputable section

namespace ActualGaussianWeberOddNormGeneric318

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberGaussLocalization318
open ActualGaussianWeberTranslationFunctionField318 ActualGaussianWeberPlaceEquivariance318
open ActualGaussianWeberStockCoordinateHom318 ActualGaussianWeberQuarterTurn318
open ActualGaussianWeberGaussianScalarSpecialization318 ActualGaussianWeberOrdinarySlope318

variable {K L : Type*} [Field K] [Field L] [DecidableEq K] [DecidableEq L]

/-- The exact rational point (0,0) on the literal stock curve. -/
@[expose] def T₀ (hK : (2:K)≠0) : WP K :=
  Point.some 0 0 (nonsing_of_equation hK (by ring))

theorem T₀_ne (hK : (2:K)≠0) : T₀ hK≠0 := Point.some_ne_zero _

theorem T₀_two (hK : (2:K)≠0) : T₀ hK+T₀ hK=0 := by
  unfold T₀
  exact Point.add_of_Y_eq rfl (by rw [literal_negY,neg_zero])

theorem quarter_T₀ (hK : (2:K)≠0) (i : K) (hi : i^2= -1) :
    turn hK i hi (T₀ hK)=T₀ hK := by
  unfold T₀
  rw [turn_some]
  exact ActualGaussianWeberStockCoordinateHom318.some_congr (neg_zero) (mul_zero _)

theorem norm_odd {a b p : ℤ} (h : a^2+b^2=p) (hp : Odd p) : Odd (a+b) := by
  have h₂ : ∀ r : ZMod 2, r^2=r := by decide
  have hp' : (p:ZMod 2)=1 := ZMod.intCast_eq_one_iff_odd.mpr hp
  apply ZMod.intCast_eq_one_iff_odd.mp
  have e := congrArg (fun z : ℤ => (z:ZMod 2)) h
  simp only [Int.cast_add,Int.cast_pow,h₂] at e ⊢
  exact e.trans hp'

theorem odd_scalar_T₀ (hK : (2:K)≠0) (i : K) (hi : i^2= -1) (a b : ℤ)
    (h : Odd (a+b)) : gaussian hK i hi a b (T₀ hK)=T₀ hK := by
  change a • T₀ hK+b • turn hK i hi (T₀ hK)=T₀ hK
  obtain ⟨m,hm⟩ := h
  have hm' : a+b=m*2+1 := by omega
  have ht : (2:ℤ) • T₀ hK=0 := by rw [two_zsmul,T₀_two]
  rw [quarter_T₀,←add_zsmul,hm',add_zsmul,mul_zsmul,ht,smul_zero,one_zsmul,zero_add]

private theorem coordinate_turn (f : K→+*L) (hK : (2:K)≠0) (hL : (2:L)≠0)
    (i : K) (j : L) (hi : i^2= -1) (hj : j^2= -1) (h : f i=j) (P : WP K) :
    coordinateHom f hL (turn hK i hi P)=turn hL j hj (coordinateHom f hL P) := by
  cases P with
  | zero => rfl
  | some x y hP =>
    change onCurvePoint f hL (turn hK i hi (Point.some x y hP))=
      turn hL j hj (onCurvePoint f hL (Point.some x y hP))
    rw [turn_some,point_some f hL hP,turn_some,point_some f hL]
    exact ActualGaussianWeberStockCoordinateHom318.some_congr (map_neg _ _) (by rw [map_mul,h])

theorem coordinate_gaussian (f : K→+*L) (hK : (2:K)≠0) (hL : (2:L)≠0)
    (i : K) (j : L) (hi : i^2= -1) (hj : j^2= -1)
    (h : f i=j) (a b : ℤ) (P : WP K) :
    coordinateHom f hL (gaussian hK i hi a b P)=
      gaussian hL j hj a b (coordinateHom f hL P) := by
  change coordinateHom f hL (a • P+b • turn hK i hi P)=
    a • coordinateHom f hL P+b • turn hL j hj (coordinateHom f hL P)
  rw [map_add,map_zsmul,map_zsmul,coordinate_turn f hK hL i j hi hj h]

section FunctionField

variable (k : Type*) [Field k] [DecidableEq (FunctionField k)]

theorem function_two_ne (h2 : (2:k)≠0) : (2:FunctionField k)≠0 := by
  intro h
  apply h2
  apply (constGeneric k).injective
  rw [map_zero,map_ofNat]
  exact h

@[expose] def genericPoint (h2 : (2:k)≠0) : WP (FunctionField k) :=
  Point.some (xGeneric k) (yGeneric k)
    (nonsing_of_equation (function_two_ne k h2) (equation_generic k))

/-- The field-coordinate involution of the generic point is *exactly*
addition of the same nonzero 2-torsion point, checked using the stock
secant and reflected y-coordinate. -/
theorem translate_generic_point (h2 : (2:k)≠0) :
    coordinateHom (translateFrac k) (function_two_ne k h2) (genericPoint k h2)=
      genericPoint k h2+T₀ (function_two_ne k h2) := by
  let x := xGeneric k
  let y := yGeneric k
  let e := (curve (FunctionField k)).toAffine
  have hx : x≠0 := xGeneric_ne k
  have hE : y^2=x^3-x := equation_generic k
  let hP := nonsing_of_equation (function_two_ne k h2) hE
  let hT := nonsing_of_equation (function_two_ne k h2)
    (show (0:FunctionField k)^2=0^3-0 by ring)
  have hbr : ¬(x=0 ∧ y=e.negY 0 0) := fun h => hx h.1
  change onCurvePoint (translateFrac k) (function_two_ne k h2) (Point.some x y hP)=
    Point.some x y hP+Point.some 0 0 hT
  rw [point_some,Point.add_some hbr]
  have hSlope : e.slope x 0 y 0=y/x := by rw [slope_of_X_ne hx,sub_zero,sub_zero]
  have hX : e.addX x 0 (e.slope x 0 y 0)= -1/x := by
    rw [hSlope,literal_addX,sub_zero,div_pow,hE]
    field_simp [hx] <;> ring
  have hY : e.addY x 0 y (e.slope x 0 y 0)=y/x^2 := by
    rw [literal_addY,hX,hSlope]
    field_simp [hx] <;> ring
  exact ActualGaussianWeberStockCoordinateHom318.some_congr
    ((translate_fraction_x k).trans hX.symm) ((translate_fraction_y k).trans hY.symm)

/-- Purely algebraic odd-norm nonvanishing at the actual generic
point. The field translation fixes the chosen Gaussian i in the
constant field. If the generic image were infinity, its translate
would be infinity too, contradicting the surviving exact T₀. -/
theorem odd_generic_nonorigin (h2 : (2:k)≠0) (i : k) (hi : i^2= -1)
    (a b p : ℤ) (hN : a^2+b^2=p) (hp : Odd p) :
    gaussian (function_two_ne k h2) (constGeneric k i)
      (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi)
      a b (genericPoint k h2) ≠ 0 := by
  let hF := function_two_ne k h2
  let j := constGeneric k i
  have hj : j^2= -1 := by simpa only [j,map_pow,map_neg,map_one] using congrArg (constGeneric k) hi
  let G := gaussian hF j hj a b
  let F := coordinateHom (translateFrac k) hF
  change G (genericPoint k h2)≠0
  intro h
  have hComm : F (G (genericPoint k h2))=G (F (genericPoint k h2)) :=
    coordinate_gaussian (translateFrac k) hF hF j j hj hj (translate_fraction_const k i) a b _
  have hTrans : F (genericPoint k h2)=genericPoint k h2+T₀ hF := translate_generic_point k h2
  have hFixed : G (T₀ hF)=T₀ hF := odd_scalar_T₀ hF j hj a b (norm_odd hN hp)
  rw [h,map_zero,hTrans,map_add,h,hFixed,zero_add] at hComm
  exact T₀_ne hF hComm.symm

end FunctionField

end ActualGaussianWeberOddNormGeneric318
