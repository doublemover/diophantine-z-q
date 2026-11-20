module
public import CTOriginalGeometricPointTransport318
public import CTOriginalGeometricGaloisAction318
public import ActualTwoDescentFieldMapNonzero318
import all CTOriginalEllipticModel318
import all CTOriginalFiniteWeierstrassCarrier318
import all CTOriginalPointCoordinates318
import all CTOriginalGeometricGaloisAction318
public section
noncomputable section
namespace ActualTwoDescentGeometricRestrictionAction318
set_option maxHeartbeats 16000000

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318

open ActualTwoDescentGeometricPointTransport318 ActualTwoDescentClosureFieldEmbedding318
open ActualTwoDescentFinitePointCardinality318 ActualTwoDescentSquareClassFieldMap318
variable {L : Type} [Field L] [CharZero L] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _

open ActualTwoDescentFieldGaloisPointAction318
lemma actual_galois_point_coordinates (n : F) (hn : n ≠ 0) (σ : Gal) (P : Point (algebraMap F Qbar n)) :
    pointCoordinates (algebraMap F Qbar n) (galoisPointHom σ n hn P)=
      Option.map (fun z : Qbar × Qbar =>
        ((show Qbar ≃ₐ[F] Qbar from σ) z.1, (show Qbar ≃ₐ[F] Qbar from σ) z.2))
        (pointCoordinates (algebraMap F Qbar n) P) := by
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

end ActualTwoDescentGeometricRestrictionAction318
