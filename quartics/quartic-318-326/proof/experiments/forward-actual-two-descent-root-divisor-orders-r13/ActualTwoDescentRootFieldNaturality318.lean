module
public import ActualTwoDescentActualEllipticFieldMap318
public section
noncomputable section
namespace ActualTwoDescentRootFieldNaturality318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentSimpleRootCoordinates318
open ActualTwoDescentAdjustedChordSquares318 ActualTwoDescentRootKummerHom318
open ActualTwoDescentSquareClassFieldMap318 ActualTwoDescentActualEllipticFieldMap318
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]
variable [DecidableEq K] [DecidableEq L]

def simpleRootMap (f : K →+* L) {n : K} (R : SimpleRoot n) : SimpleRoot (f n) where
  root := f R.root
  equation := by
    simpa only [map_mul,map_sub,map_add,map_ofNat,map_zero] using congrArg f R.equation
  simple := by
    simpa only [map_sub,map_add,map_mul,map_pow,map_ofNat] using field_map_ne_zero f R.simple

lemma actual_root_derivative_map (f : K →+* L) {n : K} (R : SimpleRoot n) :
    rootDerivative (simpleRootMap f R)=f (rootDerivative R) := by
  simp only [rootDerivative,simpleRootMap,map_sub,map_add,map_mul,map_pow,map_ofNat]

lemma actual_adjusted_map (f : K →+* L) (D u : K) :
    adjusted (f D) (f u)=f (adjusted D u) := by
  by_cases hu : u=0
  · simp [adjusted,hu]
  · simp [adjusted,hu,field_map_ne_zero f hu]

lemma actual_root_coordinate_map (f : K →+* L) (n : K) (hn : n ≠ 0)
    (R : SimpleRoot n) (P : Point n) :
    rootCoordinate (simpleRootMap f R) (ellipticFieldMap f n hn P)=f (rootCoordinate R P) := by
  cases P with
  | zero => exact (map_one f).symm
  | some x y h =>
    change adjusted (rootDerivative (simpleRootMap f R)) (f x-f R.root)=
      f (adjusted (rootDerivative R) (x-R.root))
    rw [actual_root_derivative_map,←map_sub,actual_adjusted_map]

lemma actual_root_class_map (f : K →+* L) (n : K) (hn : n ≠ 0)
    (R : SimpleRoot n) (P : Point n) :
    rootClass (simpleRootMap f R) (ellipticFieldMap f n hn P)=squareClassMap f (rootClass R P) := by
  unfold rootClass
  rw [actual_squareclass_map_value]
  congr 1
  exact actual_root_coordinate_map f n hn R P

lemma actual_first_root_map (f : K →+* L) (n : K) (hn : n ≠ 0) :
    simpleRootMap f (firstRoot n hn)=firstRoot (f n) (field_map_ne_zero f hn) := by
  simp only [simpleRootMap,firstRoot,map_mul,map_neg,map_ofNat]

lemma actual_second_root_map (f : K →+* L) (n : K) (hn : n ≠ 0) :
    simpleRootMap f (secondRoot n hn)=secondRoot (f n) (field_map_ne_zero f hn) := by
  rfl

end ActualTwoDescentRootFieldNaturality318
