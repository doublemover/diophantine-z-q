module
public import ActualTwoDescentSelmerInActualHOne318
public section
noncomputable section
namespace ActualTwoDescentFullEllipticRepresentation318
set_option maxHeartbeats 16000000

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldHalvingCocycle318
open ActualTwoDescentFieldHalvingChoiceIndependence318 ActualTwoDescentFieldGaloisLocallyConstant318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldActualCohomologicalImage318
open groupCohomology

/-- The ACTUAL nontrivial Galois action on the entire geometric elliptic group. -/
def fullEllipticRepresentation (n : F) (hn : n ≠ 0) :
    Representation ℤ Gal (Point (algebraMap F Qbar n)) where
  toFun σ := (galoisPointHom σ n hn).toIntLinearMap
  map_one' := by
    ext P
    exact actual_galois_one n hn P
  map_mul' σ τ := by
    ext P
    exact actual_galois_mul σ τ n hn P

def fullEllipticRep (n : F) (hn : n ≠ 0) : Rep ℤ Gal := Rep.of (fullEllipticRepresentation n hn)

lemma actual_full_action (n : F) (hn : n ≠ 0) (σ : Gal) (P : Point (algebraMap F Qbar n)) :
    (fullEllipticRep n hn).ρ σ P=galoisPointHom σ n hn P := rfl

end ActualTwoDescentFullEllipticRepresentation318
