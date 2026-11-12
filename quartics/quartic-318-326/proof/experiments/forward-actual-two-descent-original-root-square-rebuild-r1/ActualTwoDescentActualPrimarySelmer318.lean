module
public import ActualTwoDescentPrimaryFullClass318
public section
noncomputable section
namespace ActualTwoDescentActualPrimarySelmer318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldHalvingCocycle318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentFullEllipticHOneKernel318
open groupCohomology
open ActualTwoDescentPowerValuedCocycles318 ActualTwoDescentPowerTorsionBoundaries318
open ActualTwoDescentGeometricPowerTorsion318 ActualTwoDescentFullBoundaryHom318
open ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318 ActualTwoDescentHigherFullLifting318

open ActualTwoDescentPrimaryGeometricCocycles318 ActualTwoDescentPrimaryGeometricBoundary318
open ActualTwoDescentActualShaDefinition318 ActualTwoDescentPrimaryFullClass318
open ActualTwoDescentShaRepresentativeIndependence318

/-- Actual full primary Selmer classes: actual primary crossed cocycles with genuinely trivial full-H1 restrictions at every place. The local finite-level Kummer characterization is proved below. -/
def actualPrimarySelmer (n : ℚ) (hn : n ≠ 0) : AddSubgroup (continuousPrimaryHOne n hn) where
  carrier := {x | ∃ z : primaryCocycles n hn, primaryClass n hn z=x ∧ EverywhereLocallyTrivial n hn z.val}
  zero_mem' := ⟨0,map_zero _,by constructor <;> simp [EverywhereLocallyTrivial,map_zero]⟩
  add_mem' := by
    rintro x y ⟨z,rfl,hzR,hzp⟩ ⟨w,rfl,hwR,hwp⟩
    refine ⟨z+w,map_add _ _ _,?_,?_⟩
    · rw [map_add,map_add,hzR,hwR,zero_add]
    · intro p _; rw [map_add,map_add,hzp p,hwp p,zero_add]
  neg_mem' := by
    rintro x ⟨z,rfl,hzR,hzp⟩
    refine ⟨-z,map_neg _ _,?_,?_⟩
    · rw [map_neg,map_neg,hzR,neg_zero]
    · intro p _; rw [map_neg,map_neg,hzp p,neg_zero]

lemma actual_primary_selmer_iff_sha (n : ℚ) (hn : n ≠ 0) (x : continuousPrimaryHOne n hn) :
    x ∈ actualPrimarySelmer n hn ↔ primaryFullClass n hn x ∈ actualSha n hn := by
  constructor
  · rintro ⟨z,rfl,hz⟩
    exact ⟨z.val,rfl,hz⟩
  · intro hx
    obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x
    exact ⟨z,rfl,(actual_sha_class_iff n hn z.val).mp hx⟩

end ActualTwoDescentActualPrimarySelmer318
