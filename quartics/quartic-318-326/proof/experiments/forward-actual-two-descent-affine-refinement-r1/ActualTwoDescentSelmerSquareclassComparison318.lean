module
public import ActualTwoDescentCohomologicalSelmer318
public section
noncomputable section
namespace ActualTwoDescentSelmerSquareclassComparison318
set_option maxHeartbeats 16000000

open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldContinuousTorsionCoordinates318
open ActualTwoDescentFieldActualCohomologicalImage318 ActualTwoDescentFieldImageCriterion318
open ActualTwoDescentContinuousCocycleRestriction318 ActualTwoDescentCocycleRestrictionCoordinates318
open ActualTwoDescentCohomologicalSelmer318 ActualTwoDescentAllPlacesIntersection318
open ActualTwoDescentSquareClassFieldMap318 ActualTwoDescentLocalImageSubgroup318
variable {F L : Type} [Field F] [Field L] [CharZero F] [CharZero L] [DecidableEq F] [DecidableEq L]

lemma actual_local_cocycle_condition_iff (f : F →+* L) (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) :
    cocycleRestriction f n hn χ ∈ rationalCocycleImage (f n) (field_map_ne_zero f hn) ↔
      continuousTorsionSquareclasses n hn χ ∈ localImagePullback f n hn := by
  have h := actual_field_image_criterion (f n) (field_map_ne_zero f hn)
    (continuousTorsionSquareclasses (f n) (field_map_ne_zero f hn) (cocycleRestriction f n hn χ))
  rw [(continuousTorsionSquareclasses (f n) (field_map_ne_zero f hn)).symm_apply_apply,
    actual_cocycle_restriction_squareclasses] at h
  exact h

local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- Genuine cohomological Selmer membership is EXACTLY the original all-place actual-image intersection. -/
theorem actual_selmer_squareclass_iff (n : ℚ) (hn : n ≠ 0) (χ : continuousCocycles n) :
    χ ∈ cohomologicalSelmer n hn ↔ continuousTorsionSquareclasses n hn χ ∈ allPlacesImage n hn := by
  constructor
  · rintro ⟨hR,hp⟩
    exact ⟨(actual_local_cocycle_condition_iff (algebraMap ℚ ℝ) n hn χ).mp hR,
      fun p _ => (actual_local_cocycle_condition_iff (algebraMap ℚ (ℚ_[p])) n hn χ).mp (hp p)⟩
  · rintro ⟨hR,hp⟩
    exact ⟨(actual_local_cocycle_condition_iff (algebraMap ℚ ℝ) n hn χ).mpr hR,
      fun p _ => (actual_local_cocycle_condition_iff (algebraMap ℚ (ℚ_[p])) n hn χ).mpr (hp p)⟩

def selmerSquareclassEquiv (n : ℚ) (hn : n ≠ 0) : cohomologicalSelmer n hn ≃* allPlacesImage n hn where
  toFun χ := ⟨continuousTorsionSquareclasses n hn χ,(actual_selmer_squareclass_iff n hn χ).mp χ.property⟩
  invFun z := ⟨(continuousTorsionSquareclasses n hn).symm z,(actual_selmer_squareclass_iff n hn _).mpr (by
    rw [(continuousTorsionSquareclasses n hn).apply_symm_apply]
    exact z.property)⟩
  left_inv χ := Subtype.ext ((continuousTorsionSquareclasses n hn).symm_apply_apply χ)
  right_inv z := Subtype.ext ((continuousTorsionSquareclasses n hn).apply_symm_apply z)
  map_mul' χ ψ := Subtype.ext ((continuousTorsionSquareclasses n hn).map_mul χ ψ)

end ActualTwoDescentSelmerSquareclassComparison318
