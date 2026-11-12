module
public import ActualTwoDescentFieldGaloisCoordinateHom318
public section
noncomputable section
namespace ActualTwoDescentFieldAllTorsionGaloisComparison318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentTorsionKummerValues318 ActualTwoDescentActualTorsionPoint318
open ActualTwoDescentFieldTorsionAdditionTable318 ActualTwoDescentFieldGaloisCoordinateHom318
open ActualTwoDescentFieldFirstTorsionGaloisComparison318 ActualTwoDescentFieldLastTorsionGaloisComparison318

lemma actual_zero_galois_comparison (n : F) (hn : n ≠ 0) :
    ellipticGaloisCoordinatesHom n hn (Multiplicative.ofAdd (0 : Point n))=
      scalarKummerCoordinatesHom n hn (Multiplicative.ofAdd (0 : Point n)) := by
  change ellipticGaloisCoordinatesHom n hn 1=scalarKummerCoordinatesHom n hn 1
  rw [map_one,map_one]

lemma actual_zero_torsion_galois_comparison (n : F) (hn : n ≠ 0) :
    ellipticGaloisCoordinatesHom n hn (Multiplicative.ofAdd (zeroTorsion n hn))=
      scalarKummerCoordinatesHom n hn (Multiplicative.ofAdd (zeroTorsion n hn)) := by
  rw [←actual_first_last_sum n hn]
  change ellipticGaloisCoordinatesHom n hn (Multiplicative.ofAdd (firstTorsion n hn)*Multiplicative.ofAdd (torsionPoint n hn))=
    scalarKummerCoordinatesHom n hn (Multiplicative.ofAdd (firstTorsion n hn)*Multiplicative.ofAdd (torsionPoint n hn))
  rw [map_mul,map_mul]
  exact congrArg₂ (·*·) (actual_first_torsion_galois_comparison n hn) (actual_last_torsion_galois_comparison n hn)

end ActualTwoDescentFieldAllTorsionGaloisComparison318
