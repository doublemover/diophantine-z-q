module
public import ActualTwoDescentFieldLastTorsionGaloisComparison318
public section
noncomputable section
namespace ActualTwoDescentFieldGaloisCoordinateHom318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentFieldSquarePairGaloisEquivalence318 ActualTwoDescentFieldScalarConnectingHom318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldContinuousTorsionCoordinates318

def ellipticGaloisCoordinatesHom (n : F) (hn : n ≠ 0) :
    Multiplicative (Point n) →* ((continuousCharacters (F:=F)) × (continuousCharacters (F:=F))) :=
  (continuousTorsionCoordinates n hn).toMonoidHom.comp (continuousConnectingHom n hn)

def scalarKummerCoordinatesHom (n : F) (hn : n ≠ 0) :
    Multiplicative (Point n) →* ((continuousCharacters (F:=F)) × (continuousCharacters (F:=F))) :=
  (squarePairGaloisEquiv (F:=F)).toMonoidHom.comp (kummerHom n hn)

lemma actual_galois_coordinates_value (n : F) (hn : n ≠ 0) (P : Point n) :
    ellipticGaloisCoordinatesHom n hn (Multiplicative.ofAdd P)=
      cocyclePair n hn (continuousConnectingHom n hn (Multiplicative.ofAdd P)) := rfl
lemma actual_scalar_coordinates_value (n : F) (hn : n ≠ 0) (P : Point n) :
    scalarKummerCoordinatesHom n hn (Multiplicative.ofAdd P)=(squarePairGaloisEquiv (F:=F)) (kummerClass n hn P) := rfl

end ActualTwoDescentFieldGaloisCoordinateHom318
