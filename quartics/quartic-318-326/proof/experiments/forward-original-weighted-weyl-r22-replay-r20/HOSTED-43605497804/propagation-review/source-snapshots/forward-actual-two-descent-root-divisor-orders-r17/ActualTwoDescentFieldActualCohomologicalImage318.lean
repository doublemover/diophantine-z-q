module
public import ActualTwoDescentFieldCocycleSquareclassCompatibility318
public section
noncomputable section
namespace ActualTwoDescentFieldActualCohomologicalImage318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldContinuousTorsionCoordinates318
open ActualTwoDescentFieldCocycleSquareclassCompatibility318 ActualTwoDescentLocalImageSubgroup318

/-- Actual base-field elliptic image in the ACTUAL continuous cocycle group. -/
def rationalCocycleImage (n : F) (hn : n ≠ 0) : Subgroup (continuousCocycles n) := (continuousConnectingHom n hn).range

/-- Full literal original Kummer image is the image of the actual cohomological connecting map. -/
theorem actual_cohomological_image_identity (n : F) (hn : n ≠ 0) :
    (rationalCocycleImage n hn).map (continuousTorsionSquareclasses n hn).toMonoidHom=actualKummerImage n hn := by
  ext z
  constructor
  · rintro ⟨f,⟨P,hP⟩,hf⟩
    apply (actual_kummer_image_iff n hn z).mpr
    refine ⟨P.toAdd,?_⟩
    rw [←hf,←hP]
    exact (actual_cocycle_squareclass_compatibility n hn P.toAdd).symm
  · intro hz
    obtain ⟨P,hP⟩ := (actual_kummer_image_iff n hn z).mp hz
    refine ⟨continuousConnectingHom n hn (Multiplicative.ofAdd P),⟨Multiplicative.ofAdd P,rfl⟩,?_⟩
    exact (actual_cocycle_squareclass_compatibility n hn P).trans hP

end ActualTwoDescentFieldActualCohomologicalImage318
