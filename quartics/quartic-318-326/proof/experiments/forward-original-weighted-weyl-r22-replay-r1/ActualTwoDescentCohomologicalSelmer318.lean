module
public import ActualTwoDescentTorsionTransferCoordinates318
public section
noncomputable section
namespace ActualTwoDescentCohomologicalSelmer318
set_option maxHeartbeats 16000000

open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldActualCohomologicalImage318
open ActualTwoDescentContinuousCocycleRestriction318 ActualTwoDescentSquareClassFieldMap318
open ActualTwoDescentEllipticRestrictionNaturality318
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- Genuine2-Selmer conditions: ACTUAL continuous Galois restriction lies in the ACTUAL local elliptic connecting image. -/
def cohomologicalSelmer (n : ℚ) (hn : n ≠ 0) : Subgroup (continuousCocycles n) where
  carrier := {z | z ∈ (rationalCocycleImage ((algebraMap ℚ ℝ) n) (field_map_ne_zero _ hn)).comap
      (cocycleRestriction (algebraMap ℚ ℝ) n hn) ∧
    ∀ (p : ℕ) [Fact p.Prime], z ∈ (rationalCocycleImage ((algebraMap ℚ (ℚ_[p])) n) (field_map_ne_zero _ hn)).comap
      (cocycleRestriction (algebraMap ℚ (ℚ_[p])) n hn)}
  one_mem' := ⟨Subgroup.one_mem _,fun p _ => Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hxR,hxp⟩ ⟨hyR,hyp⟩
    exact ⟨Subgroup.mul_mem _ hxR hyR,fun p _ => Subgroup.mul_mem _ (hxp p) (hyp p)⟩
  inv_mem' := by
    rintro x ⟨hxR,hxp⟩
    exact ⟨Subgroup.inv_mem _ hxR,fun p _ => Subgroup.inv_mem _ (hxp p)⟩

lemma actual_global_cocycle_image_le_selmer (n : ℚ) (hn : n ≠ 0) :
    rationalCocycleImage n hn ≤ cohomologicalSelmer n hn := by
  intro z hz
  exact ⟨actual_rational_cocycle_image_restricts (algebraMap ℚ ℝ) n hn hz,
    fun p _ => actual_rational_cocycle_image_restricts (algebraMap ℚ (ℚ_[p])) n hn hz⟩

end ActualTwoDescentCohomologicalSelmer318
