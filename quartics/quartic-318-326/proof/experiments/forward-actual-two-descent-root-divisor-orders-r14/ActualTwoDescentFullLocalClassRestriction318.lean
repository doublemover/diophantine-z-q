module
public import ActualTwoDescentFullCocycleRestriction318
public section
noncomputable section
namespace ActualTwoDescentFullLocalClassRestriction318
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

open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticHOneKernel318 ActualTwoDescentFullCocycleRestriction318
open ActualTwoDescentGeometricPointTransport318 ActualTwoDescentSquareClassFieldMap318
variable {L : Type} [Field L] [CharZero L] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _

/-- Actual restriction respects cohomology, established by actual geometric coboundary base change. -/
lemma actual_full_local_class_eq (f : F →+* L) (n : F) (hn : n ≠ 0)
    (z w : continuousFullCocycles n hn) (h : fullClassHom n hn z=fullClassHom n hn w) :
    fullClassHom (f n) (field_map_ne_zero f hn) (fullCocycleRestriction f n hn z)=
      fullClassHom (f n) (field_map_ne_zero f hn) (fullCocycleRestriction f n hn w) := by
  have hz : fullClassHom n hn (z-w)=0 := by rw [map_sub,h,sub_self]
  obtain ⟨Q,hQ⟩ := (actual_full_class_zero n hn (z-w)).mp hz
  have he : z-w=fullBoundary n hn Q := by apply Subtype.ext; apply Subtype.ext; exact funext hQ
  apply sub_eq_zero.mp
  rw [←map_sub,←map_sub,he,actual_full_restriction_boundary,actual_full_boundary_zero]

end ActualTwoDescentFullLocalClassRestriction318
