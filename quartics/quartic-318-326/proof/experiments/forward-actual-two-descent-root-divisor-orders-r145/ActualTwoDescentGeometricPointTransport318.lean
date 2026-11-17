module
public import ActualTwoDescentFullHOneTwoSurjectivity318
public section
noncomputable section
namespace ActualTwoDescentGeometricPointTransport318
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

open ActualTwoDescentFinitePointCardinality318
variable {L : Type} [Field L] [CharZero L] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _

def parameterTransport {K : Type} [Field K] [DecidableEq K] (n m : K) (h : n=m) : Point n →+ Point m := by
  subst m
  exact AddMonoidHom.id _

lemma actual_transport_coordinates {K : Type} [Field K] [CharZero K] [DecidableEq K]
    (n m : K) (h : n=m) (P : Point n) :
    pointCoordinates m (parameterTransport n m h P)=pointCoordinates n P := by subst m; rfl

open ActualTwoDescentClosureFieldEmbedding318 ActualTwoDescentActualEllipticFieldMap318
/-- Actual closure base change, followed only by the proved equality of the original parameter. -/
def closurePointMap (f : F →+* L) (n : F) (hn : n ≠ 0) :
    Point (algebraMap F Qbar n) →+ Point (algebraMap L (AlgebraicClosure L) (f n)) :=
  (parameterTransport _ _ (actual_closure_map_base f n)).comp
    (ellipticFieldMap (closureMap f) _ (rational_parameter_ne n hn))

lemma actual_closure_point_coordinates (f : F →+* L) (n : F) (hn : n ≠ 0) (P : Point (algebraMap F Qbar n)) :
    pointCoordinates (algebraMap L (AlgebraicClosure L) (f n)) (closurePointMap f n hn P)=
      Option.map (fun z : Qbar × Qbar => (closureMap f z.1,closureMap f z.2)) (pointCoordinates (algebraMap F Qbar n) P) := by
  change pointCoordinates _ (parameterTransport _ _ _ (ellipticFieldMap _ _ _ P))=_
  rw [actual_transport_coordinates]
  cases P <;> rfl

lemma actual_closure_point_injective (f : F →+* L) (n : F) (hn : n ≠ 0) : Function.Injective (closurePointMap f n hn) := by
  intro P Q h
  apply actual_point_coordinates_injective _
  have he := congrArg (pointCoordinates _) h
  rw [actual_closure_point_coordinates,actual_closure_point_coordinates] at he
  cases P with
  | zero => cases Q <;> simp_all [pointCoordinates]
  | some x y hx =>
    cases Q with
    | zero => simp_all [pointCoordinates]
    | some u v hu =>
      have huv : closureMap f x=closureMap f u ∧ closureMap f y=closureMap f v := by simpa [pointCoordinates] using he
      simp only [pointCoordinates]
      exact congrArg some (Prod.ext ((closureMap f).injective huv.1) ((closureMap f).injective huv.2))

end ActualTwoDescentGeometricPointTransport318
