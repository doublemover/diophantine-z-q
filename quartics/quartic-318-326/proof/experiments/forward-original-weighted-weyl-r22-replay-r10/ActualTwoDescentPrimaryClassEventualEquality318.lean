module
public import ActualTwoDescentHigherCohomologyDirectedSystem318
public section
noncomputable section
namespace ActualTwoDescentPrimaryClassEventualEquality318
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
open ActualTwoDescentFiniteLevelIntoPrimary318 ActualTwoDescentHigherCohomologyDirectedMaps318

/-- Equality in actual primary H1 is witnessed by an actual torsion coboundary at a common finite level. -/
lemma actual_primary_class_eventual_zero (n : F) (hn : n ≠ 0) (i : ℕ) (x : continuousPowerHOne n hn i)
    (hx : powerIntoPrimaryHOne n hn i x=0) :
    ∃ j : ℕ, ∃ h : i ≤ j, higherCohomologyMap n hn i j h x=0 := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x
  have hm : powerIntoPrimaryCocycles n hn i z ∈ (primaryBoundaryHom n hn).range :=
    (QuotientAddGroup.eq_zero_iff _).mp hx
  obtain ⟨T,hT⟩ := hm
  obtain ⟨k,hk⟩ := T.property
  let j := max i k
  let U : geometricPowerTorsion n j := ⟨T.val,actual_nsmul_power_mono (le_max_right i k) hk⟩
  refine ⟨j,le_max_left i k,?_⟩
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨U,?_⟩
  apply Subtype.ext
  exact congrArg Subtype.val hT

end ActualTwoDescentPrimaryClassEventualEquality318
