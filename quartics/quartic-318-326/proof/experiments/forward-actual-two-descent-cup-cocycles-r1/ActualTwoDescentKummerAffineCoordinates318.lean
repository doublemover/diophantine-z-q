module
public import ActualTwoDescentKummerHom318
public section
noncomputable section
namespace ActualTwoDescentKummerAffineCoordinates318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentSimpleRootCoordinates318
open ActualTwoDescentAdjustedChordSquares318
variable [DecidableEq K]

lemma actual_first_coordinate (n x y : K) (hn : n ≠ 0)
    (h : (curve n).toAffine.Nonsingular x y) (hA : x+3*n ≠ 0) :
    rootCoordinate (firstRoot n hn) (.some x y h)=x+3*n := by
  rw [root_coordinate_some _ _ (by intro he; apply hA; change x= -3*n at he; rw [he]; ring)]
  dsimp [firstRoot]
  ring

lemma actual_second_coordinate (n x y : K) (hn : n ≠ 0)
    (h : (curve n).toAffine.Nonsingular x y) (hB : x-n ≠ 0) :
    rootCoordinate (secondRoot n hn) (.some x y h)=x-n := by
  exact root_coordinate_some _ _ (sub_ne_zero.mp hB)

lemma actual_first_at_root (n y : K) (hn : n ≠ 0)
    (h : (curve n).toAffine.Nonsingular (-3*n) y) :
    rootCoordinate (firstRoot n hn) (.some (-3*n) y h)=12*n^2 := by
  simp only [rootCoordinate,firstRoot,adjusted,sub_self,if_pos rfl,rootDerivative]
  ring

lemma actual_second_at_root (n y : K) (hn : n ≠ 0)
    (h : (curve n).toAffine.Nonsingular n y) :
    rootCoordinate (secondRoot n hn) (.some n y h)=4*n^2 := by
  simp only [rootCoordinate,secondRoot,adjusted,sub_self,if_pos rfl,rootDerivative]
  ring

end ActualTwoDescentKummerAffineCoordinates318
