module
public import ActualTwoDescentFullGaloisComparison318
public section
noncomputable section
namespace ActualTwoDescentCocycleSquareclassCompatibility318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentSquarePairGaloisEquivalence318 ActualTwoDescentFullGaloisComparison318
open ActualTwoDescentGaloisCoordinateHom318 ActualTwoDescentContinuousGaloisCocycles318
open ActualTwoDescentContinuousTorsionCoordinates318

/-- The actual full Galois connecting class has EXACTLY the original literal squareclass pair. -/
theorem actual_cocycle_squareclass_compatibility (n : ℚ) (hn : n ≠ 0) (P : Point n) :
    continuousTorsionSquareclasses n hn (continuousConnectingHom n hn (Multiplicative.ofAdd P))=kummerClass n hn P := by
  apply squarePairGaloisEquiv.injective
  change squarePairGaloisEquiv (squarePairGaloisEquiv.symm
    (cocyclePair n hn (continuousConnectingHom n hn (Multiplicative.ofAdd P))))=_
  rw [squarePairGaloisEquiv.apply_symm_apply]
  exact actual_full_galois_comparison n hn P

end ActualTwoDescentCocycleSquareclassCompatibility318
