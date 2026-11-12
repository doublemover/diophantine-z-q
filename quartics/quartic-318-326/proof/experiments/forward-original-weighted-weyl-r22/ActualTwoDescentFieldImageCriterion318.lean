module
public import ActualTwoDescentFieldActualCohomologicalImage318
public section
noncomputable section
namespace ActualTwoDescentFieldImageCriterion318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentSquareClassQuotient318 ActualTwoDescentKummerHom318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldContinuousTorsionCoordinates318
open ActualTwoDescentFieldCocycleSquareclassCompatibility318 ActualTwoDescentFieldActualCohomologicalImage318
open ActualTwoDescentLocalImageSubgroup318
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]

/-- Exact local/global-field image criterion in the ACTUAL continuous E[2] cocycle group. -/
theorem actual_field_image_criterion (n : F) (hn : n ≠ 0) (z : SquareClass F × SquareClass F) :
    (continuousTorsionSquareclasses n hn).symm z ∈ rationalCocycleImage n hn ↔ z ∈ actualKummerImage n hn := by
  constructor
  · rintro ⟨P,hP⟩
    apply (actual_kummer_image_iff n hn z).mpr
    refine ⟨P.toAdd,?_⟩
    rw [←actual_cocycle_squareclass_compatibility n hn P.toAdd,hP]
    exact (continuousTorsionSquareclasses n hn).apply_symm_apply z
  · intro hz
    obtain ⟨P,hP⟩ := (actual_kummer_image_iff n hn z).mp hz
    refine ⟨Multiplicative.ofAdd P,?_⟩
    apply (continuousTorsionSquareclasses n hn).injective
    rw [actual_cocycle_squareclass_compatibility,hP]
    exact ((continuousTorsionSquareclasses n hn).apply_symm_apply z).symm

end ActualTwoDescentFieldImageCriterion318
