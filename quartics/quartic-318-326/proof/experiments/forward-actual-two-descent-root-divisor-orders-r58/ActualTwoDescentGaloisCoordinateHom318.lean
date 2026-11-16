module
public import ActualTwoDescentLastTorsionGaloisComparison318
public section
noncomputable section
namespace ActualTwoDescentGaloisCoordinateHom318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentSquarePairGaloisEquivalence318 ActualTwoDescentScalarConnectingHom318
open ActualTwoDescentContinuousGaloisCocycles318 ActualTwoDescentContinuousTorsionCoordinates318

def ellipticGaloisCoordinatesHom (n : ℚ) (hn : n ≠ 0) :
    Multiplicative (Point n) →* (continuousCharacters × continuousCharacters) :=
  (continuousTorsionCoordinates n hn).toMonoidHom.comp (continuousConnectingHom n hn)

def scalarKummerCoordinatesHom (n : ℚ) (hn : n ≠ 0) :
    Multiplicative (Point n) →* (continuousCharacters × continuousCharacters) :=
  squarePairGaloisEquiv.toMonoidHom.comp (kummerHom n hn)

lemma actual_galois_coordinates_value (n : ℚ) (hn : n ≠ 0) (P : Point n) :
    ellipticGaloisCoordinatesHom n hn (Multiplicative.ofAdd P)=
      cocyclePair n hn (continuousConnectingHom n hn (Multiplicative.ofAdd P)) := rfl
lemma actual_scalar_coordinates_value (n : ℚ) (hn : n ≠ 0) (P : Point n) :
    scalarKummerCoordinatesHom n hn (Multiplicative.ofAdd P)=squarePairGaloisEquiv (kummerClass n hn P) := rfl

end ActualTwoDescentGaloisCoordinateHom318
