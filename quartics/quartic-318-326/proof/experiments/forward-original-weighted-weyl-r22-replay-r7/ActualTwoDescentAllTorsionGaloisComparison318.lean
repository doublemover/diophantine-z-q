module
public import ActualTwoDescentGaloisCoordinateHom318
public section
noncomputable section
namespace ActualTwoDescentAllTorsionGaloisComparison318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentTorsionKummerValues318 ActualTwoDescentActualTorsionPoint318
open ActualTwoDescentTorsionAdditionTable318 ActualTwoDescentGaloisCoordinateHom318
open ActualTwoDescentFirstTorsionGaloisComparison318 ActualTwoDescentLastTorsionGaloisComparison318

lemma actual_zero_galois_comparison (n : ℚ) (hn : n ≠ 0) :
    ellipticGaloisCoordinatesHom n hn (Multiplicative.ofAdd (0 : Point n))=
      scalarKummerCoordinatesHom n hn (Multiplicative.ofAdd (0 : Point n)) := by
  change ellipticGaloisCoordinatesHom n hn 1=scalarKummerCoordinatesHom n hn 1
  rw [map_one,map_one]

lemma actual_zero_torsion_galois_comparison (n : ℚ) (hn : n ≠ 0) :
    ellipticGaloisCoordinatesHom n hn (Multiplicative.ofAdd (zeroTorsion n hn))=
      scalarKummerCoordinatesHom n hn (Multiplicative.ofAdd (zeroTorsion n hn)) := by
  rw [←actual_first_last_sum n hn]
  change ellipticGaloisCoordinatesHom n hn (Multiplicative.ofAdd (firstTorsion n hn)*Multiplicative.ofAdd (torsionPoint n hn))=
    scalarKummerCoordinatesHom n hn (Multiplicative.ofAdd (firstTorsion n hn)*Multiplicative.ofAdd (torsionPoint n hn))
  rw [map_mul,map_mul]
  exact congrArg₂ (·*·) (actual_first_torsion_galois_comparison n hn) (actual_last_torsion_galois_comparison n hn)

end ActualTwoDescentAllTorsionGaloisComparison318
