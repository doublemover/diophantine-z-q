module
public import ActualTwoDescentEllipticDoubleQuotient318
public section
noncomputable section
namespace ActualTwoDescentLiteralKummerClasses318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentSimpleRootCoordinates318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentKummerHom318
open ActualTwoDescentRootKummerHom318 ActualTwoDescentKummerAffineCoordinates318
open ActualTwoDescentTorsionSquarePairs318
variable [DecidableEq K]

lemma actual_kummer_affine_value (n x y : K) (hn : n ≠ 0)
    (h : (curve n).toAffine.Nonsingular x y) (hA : x+3*n ≠ 0) (hB : x-n ≠ 0) :
    kummerClass n hn (.some x y h)=(classOf (x+3*n) hA,classOf (x-n) hB) := by
  apply Prod.ext
  · change classOf (rootCoordinate (firstRoot n hn) (.some x y h)) _=classOf (x+3*n) hA
    simp only [actual_first_coordinate n x y hn h hA]
  · change classOf (rootCoordinate (secondRoot n hn) (.some x y h)) _=classOf (x-n) hB
    simp only [actual_second_coordinate n x y hn h hB]

/-- Actual squareclass equality retains both literal coordinates and both
nonzero multipliers, rather than only a formal signature. -/
theorem actual_kummer_pair_iff (n x y a b : K) (hn : n ≠ 0)
    (h : (curve n).toAffine.Nonsingular x y) (hA : x+3*n ≠ 0) (hB : x-n ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    kummerClass n hn (.some x y h)=(classOf a ha,classOf b hb) ↔ SquarePair (x+3*n) (x-n) a b := by
  rw [actual_kummer_affine_value n x y hn h hA hB,Prod.mk.injEq,class_of_eq_iff,class_of_eq_iff]
  constructor
  · rintro ⟨⟨u,hu,hU⟩,⟨v,hv,hV⟩⟩
    exact ⟨u,v,hu,hv,hU,hV⟩
  · rintro ⟨u,v,hu,hv,hU,hV⟩
    exact ⟨⟨u,hu,hU⟩,⟨v,hv,hV⟩⟩

end ActualTwoDescentLiteralKummerClasses318
