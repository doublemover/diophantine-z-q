module
public import ActualTwoDescentFiniteAdjustedChordSquares318
public section
noncomputable section
namespace ActualTwoDescentFiniteSimpleRootCoordinates318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [NeZero (2 : K)] [NeZero (3 : K)]


open ActualTwoDescentFiniteEllipticModel318 ActualTwoDescentFiniteAdjustedChordSquares318
variable [DecidableEq K]

structure SimpleRoot (n : K) where
  root : K
  equation : root*(root-n)*(root+3*n)=0
  simple : 3*root^2+4*n*root-3*n^2 ≠ 0

def rootDerivative {n : K} (R : SimpleRoot n) : K := 3*R.root^2+4*n*R.root-3*n^2

def rootCoordinate {n : K} (R : SimpleRoot n) : Point n → K
  | .zero => 1
  | .some x _ _ => adjusted (rootDerivative R) (x-R.root)

lemma root_coordinate_nonzero {n : K} (R : SimpleRoot n) (P : Point n) : rootCoordinate R P ≠ 0 := by
  cases P with
  | zero => exact one_ne_zero
  | some x y h => exact adjusted_nonzero _ _ R.simple

lemma root_coordinate_some {n x y : K} (R : SimpleRoot n)
    (h : (curve n).toAffine.Nonsingular x y) (hx : x ≠ R.root) :
    rootCoordinate R (.some x y h)=x-R.root := by
  exact if_neg (sub_ne_zero.mpr hx)

/-- The first original Kummer coordinate corresponds to the retained root -3n. -/
def firstRoot (n : K) (hn : n ≠ 0) : SimpleRoot n where
  root := -3*n
  equation := by ring
  simple := by
    have he : 3*(-3*n)^2+4*n*(-3*n)-3*n^2=12*n^2 := by ring
    rw [he]
    exact mul_ne_zero good_twelve_ne (pow_ne_zero _ hn)

/-- The second original Kummer coordinate corresponds to the root n. -/
def secondRoot (n : K) (hn : n ≠ 0) : SimpleRoot n where
  root := n
  equation := by ring
  simple := by
    have he : 3*n^2+4*n*n-3*n^2=4*n^2 := by ring
    rw [he]
    exact mul_ne_zero good_four_ne (pow_ne_zero _ hn)

end ActualTwoDescentFiniteSimpleRootCoordinates318
