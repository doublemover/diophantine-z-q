module
public import ActualTwoDescentSquareClassQuotient318
public import ActualTwoDescentFiniteRootCoordinateProduct318
public section
noncomputable section
namespace ActualTwoDescentFiniteRootKummerHom318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [NeZero (2 : K)] [NeZero (3 : K)]


open ActualTwoDescentFiniteEllipticModel318 ActualTwoDescentFiniteSimpleRootCoordinates318
open ActualTwoDescentFiniteRootCoordinateProduct318 ActualTwoDescentSquareClassQuotient318
variable [DecidableEq K]

def rootClass {n : K} (R : SimpleRoot n) (P : Point n) : SquareClass K :=
  classOf (rootCoordinate R P) (root_coordinate_nonzero R P)

lemma root_class_zero {n : K} (R : SimpleRoot n) : rootClass R 0=1 := class_of_one

/-- Genuine multiplicativity on the entire elliptic group. -/
theorem actual_root_class_add {n : K} (R : SimpleRoot n) (P Q : Point n) :
    rootClass R (P+Q)=rootClass R P*rootClass R Q := by
  rw [rootClass,rootClass,rootClass,←class_of_mul]
  apply (class_of_eq_iff _ _ _ _).mpr
  obtain ⟨s,hs,h⟩ := actual_root_product_square R P Q
  refine ⟨s/(rootCoordinate R P*rootCoordinate R Q),
    div_ne_zero hs (mul_ne_zero (root_coordinate_nonzero R P) (root_coordinate_nonzero R Q)),?_⟩
  calc
    rootCoordinate R (P+Q)=s^2/(rootCoordinate R P*rootCoordinate R Q) := by
      apply (eq_div_iff (mul_ne_zero (root_coordinate_nonzero R P) (root_coordinate_nonzero R Q))).mpr
      linear_combination h
    _=(rootCoordinate R P*rootCoordinate R Q)*(s/(rootCoordinate R P*rootCoordinate R Q))^2 := by
      field_simp [root_coordinate_nonzero R P,root_coordinate_nonzero R Q]
      <;> ring

/-- Bundled homomorphism from the actual elliptic group to actual squareclasses. -/
def rootKummerHom {n : K} (R : SimpleRoot n) : Multiplicative (Point n) →* SquareClass K where
  toFun P := rootClass R P.toAdd
  map_one' := root_class_zero R
  map_mul' P Q := actual_root_class_add R P.toAdd Q.toAdd

end ActualTwoDescentFiniteRootKummerHom318
