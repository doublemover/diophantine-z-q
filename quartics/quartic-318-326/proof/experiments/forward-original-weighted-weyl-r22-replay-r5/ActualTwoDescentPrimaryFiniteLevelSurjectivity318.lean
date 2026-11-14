module
public import ActualTwoDescentFiniteLevelIntoPrimary318
public section
noncomputable section
namespace ActualTwoDescentPrimaryFiniteLevelSurjectivity318
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
open ActualTwoDescentPrimaryCocycleUniformLevel318 ActualTwoDescentFiniteLevelIntoPrimary318

/-- Every actual continuous primary cohomology class is represented at ONE finite power level, by actual compactness rather than a boundedness premise. -/
theorem actual_primary_hone_finite_level (n : F) (hn : n ≠ 0) (x : continuousPrimaryHOne n hn) :
    ∃ k : ℕ, ∃ y : continuousPowerHOne n hn k, powerIntoPrimaryHOne n hn k y=x := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨k,hk⟩ := actual_primary_cocycle_uniform_level n hn z
  exact ⟨k,powerClass n hn k ⟨z.val,hk⟩,rfl⟩

end ActualTwoDescentPrimaryFiniteLevelSurjectivity318
