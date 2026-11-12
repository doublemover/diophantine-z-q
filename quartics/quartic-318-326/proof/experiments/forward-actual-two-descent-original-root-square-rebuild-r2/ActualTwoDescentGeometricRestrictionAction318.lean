module
public import ActualTwoDescentGeometricPointTransport318
public section
noncomputable section
namespace ActualTwoDescentGeometricRestrictionAction318
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

open ActualTwoDescentGeometricPointTransport318 ActualTwoDescentClosureFieldEmbedding318
open ActualTwoDescentFinitePointCardinality318 ActualTwoDescentSquareClassFieldMap318
variable {L : Type} [Field L] [CharZero L] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _

lemma actual_galois_point_coordinates (n : F) (hn : n ≠ 0) (σ : Gal) (P : Point (algebraMap F Qbar n)) :
    pointCoordinates (algebraMap F Qbar n) (galoisPointHom σ n hn P)=
      Option.map (fun z : Qbar × Qbar => (σ z.1,σ z.2)) (pointCoordinates (algebraMap F Qbar n) P) := by
  cases P <;> rfl

/-- Actual full geometric point base change intertwines the actual nontrivial Galois actions. -/
lemma actual_closure_point_galois (f : F →+* L) (n : F) (hn : n ≠ 0)
    (σ : Field.absoluteGaloisGroup L) (P : Point (algebraMap F Qbar n)) :
    closurePointMap f n hn (galoisPointHom (Field.absoluteGaloisGroup.map f σ) n hn P)=
      galoisPointHom σ (f n) (field_map_ne_zero f hn) (closurePointMap f n hn P) := by
  apply actual_point_coordinates_injective _
  rw [actual_closure_point_coordinates,actual_galois_point_coordinates,
    actual_galois_point_coordinates,actual_closure_point_coordinates]
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [pointCoordinates,Option.map_some,actual_closure_map_galois]

lemma actual_closure_point_torsion (f : F →+* L) (n : F) (hn : n ≠ 0)
    (T : Multiplicative (closedTwoTorsion n)) :
    closurePointMap f n hn T.toAdd=
      ((ActualTwoDescentTorsionCoefficientTransfer318.torsionCoefficientTransfer f n hn T).toAdd : Point (algebraMap L (AlgebraicClosure L) (f n))) := by
  apply actual_point_coordinates_injective _
  rw [actual_closure_point_coordinates,
    ActualTwoDescentTorsionTransferCoordinates318.actual_torsion_transfer_coordinates]

end ActualTwoDescentGeometricRestrictionAction318
