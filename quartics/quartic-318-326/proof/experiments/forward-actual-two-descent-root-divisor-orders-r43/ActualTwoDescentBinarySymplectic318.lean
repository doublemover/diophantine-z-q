module
public import ActualTwoDescentSquareOneBinary318
public section
noncomputable section
namespace ActualTwoDescentBinarySymplectic318
open ActualTwoDescentSquareOneBinary318
abbrev BinaryPlane := ZMod 2 × ZMod 2

def binaryPairing (x y : BinaryPlane) : ZMod 2 := x.1*y.2-x.2*y.1

def binaryQuadratic (x : BinaryPlane) : ZMod 2 := x.1*x.2

lemma actual_binary_pairing_add_left (x y z : BinaryPlane) :
    binaryPairing (x+y) z=binaryPairing x z+binaryPairing y z := by
  dsimp [binaryPairing]; ring

lemma actual_binary_pairing_add_right (x y z : BinaryPlane) :
    binaryPairing x (y+z)=binaryPairing x y+binaryPairing x z := by
  dsimp [binaryPairing]; ring

@[simp] lemma actual_binary_pairing_zero_left (x : BinaryPlane) : binaryPairing 0 x=0 := by
  simp [binaryPairing]
@[simp] lemma actual_binary_pairing_zero_right (x : BinaryPlane) : binaryPairing x 0=0 := by
  simp [binaryPairing]
@[simp] lemma actual_binary_pairing_self (x : BinaryPlane) : binaryPairing x x=0 := by
  dsimp [binaryPairing]; ring

lemma actual_binary_pairing_symmetric (x y : BinaryPlane) : binaryPairing x y=binaryPairing y x := by
  simp only [binaryPairing,sub_eq_add_neg,actual_binary_neg]
  ring

lemma actual_binary_pairing_nondegenerate (x : BinaryPlane)
    (hx : ∀ y, binaryPairing x y=0) : x=0 := by
  have h1 := hx (0,1)
  have h2 := hx (1,0)
  apply Prod.ext
  · simpa [binaryPairing] using h1
  · simpa [binaryPairing] using h2

/-- The explicit invariant quadratic refinement needed for a continuous
self-cup coboundary. This is not a claim about a geometric theta group. -/
lemma actual_binary_quadratic_polar (x y : BinaryPlane) :
    binaryQuadratic y-binaryQuadratic (x+y)+binaryQuadratic x=binaryPairing x y := by
  rcases x with ⟨x1,x2⟩
  rcases y with ⟨y1,y2⟩
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;> decide

end ActualTwoDescentBinarySymplectic318
