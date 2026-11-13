module
public import ActualTwoDescentEllipticFieldCoordinates318
public section
noncomputable section
namespace ActualTwoDescentActualEllipticFieldMap318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticFieldCoordinates318
open ActualTwoDescentSquareClassFieldMap318
variable {L : Type*} [Field L] [CharZero L] [DecidableEq K] [DecidableEq L]

def pointMap (f : K →+* L) (n : K) (hn : n ≠ 0) : Point n → Point (f n)
  | .zero => .zero
  | .some x y h => point (f n) (f x) (f y) (field_map_ne_zero f hn)
      (actual_curve_equation_map f n x y ((curve_equation n x y).mp h.left))

lemma actual_point_map_add (f : K →+* L) (n : K) (hn : n ≠ 0) (P Q : Point n) :
    pointMap f n hn (P+Q)=pointMap f n hn P+pointMap f n hn Q := by
  cases P with
  | zero => simp only [zero_add,pointMap]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => simp only [add_zero,pointMap]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁=x₂ ∧ y₁=(curve n).toAffine.negY x₂ y₂
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2]
        dsimp [pointMap,point]
        symm
        apply WeierstrassCurve.Affine.Point.add_of_Y_eq (congrArg f hxy.1)
        rw [actual_negY_map,hxy.2]
      · have hfxy : ¬(f x₁=f x₂ ∧ f y₁=(curve (f n)).toAffine.negY (f x₂) (f y₂)) := by
          rintro ⟨hx,hy⟩
          rw [actual_negY_map] at hy
          exact hxy ⟨f.injective hx,f.injective hy⟩
        rw [WeierstrassCurve.Affine.Point.add_some hxy]
        dsimp [pointMap,point]
        rw [WeierstrassCurve.Affine.Point.add_some hfxy]
        congr 1
        · rw [actual_slope_map,actual_addX_map]
        · rw [actual_slope_map,actual_addY_map]

def ellipticFieldMap (f : K →+* L) (n : K) (hn : n ≠ 0) : Point n →+ Point (f n) where
  toFun := pointMap f n hn
  map_zero' := rfl
  map_add' := actual_point_map_add f n hn

lemma actual_elliptic_field_map_injective (f : K →+* L) (n : K) (hn : n ≠ 0) :
    Function.Injective (ellipticFieldMap f n hn) := by
  intro P Q he
  change pointMap f n hn P=pointMap f n hn Q at he
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y h => exact False.elim (point_ne_zero _ _ _ _ _ he.symm)
  | some x y h =>
    cases Q with
    | zero => exact False.elim (point_ne_zero _ _ _ _ _ he)
    | some z w h' =>
      have hxy : f x=f z ∧ f y=f w := by
        simpa only [pointMap,point,WeierstrassCurve.Affine.Point.some.injEq] using he
      have hx := hxy.1
      have hy := hxy.2
      have hxx := f.injective hx
      have hyy := f.injective hy
      subst z; subst w
      rfl

end ActualTwoDescentActualEllipticFieldMap318
