module
public import ActualTwoDescentFieldFullGaloisComparison318
public section
noncomputable section
namespace ActualTwoDescentFieldCocycleSquareclassCompatibility318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentFieldSquarePairGaloisEquivalence318 ActualTwoDescentFieldFullGaloisComparison318
open ActualTwoDescentFieldGaloisCoordinateHom318 ActualTwoDescentFieldContinuousGaloisCocycles318
open ActualTwoDescentFieldContinuousTorsionCoordinates318

/-- The actual full Galois connecting class has EXACTLY the original literal squareclass pair. -/
theorem actual_cocycle_squareclass_compatibility (n : F) (hn : n ≠ 0) (P : Point n) :
    continuousTorsionSquareclasses n hn (continuousConnectingHom n hn (Multiplicative.ofAdd P))=kummerClass n hn P := by
  apply (squarePairGaloisEquiv (F:=F)).injective
  change (squarePairGaloisEquiv (F:=F)) ((squarePairGaloisEquiv (F:=F)).symm
    (cocyclePair n hn (continuousConnectingHom n hn (Multiplicative.ofAdd P))))=_
  rw [(squarePairGaloisEquiv (F:=F)).apply_symm_apply]
  exact actual_full_galois_comparison n hn P

end ActualTwoDescentFieldCocycleSquareclassCompatibility318
