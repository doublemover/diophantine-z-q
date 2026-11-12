module
public import ActualTwoDescentPrimaryCocycleUniformLevel318
public section
noncomputable section
namespace ActualTwoDescentPrimaryGeometricBoundary318
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

open ActualTwoDescentPrimaryGeometricCocycles318

def primaryBoundary (n : F) (hn : n ≠ 0) (T : geometricPrimary n) : primaryCocycles n hn := by
  refine ⟨fullBoundary n hn T.val,?_⟩
  intro σ
  obtain ⟨k,hk⟩ := T.property
  refine ⟨k,?_⟩
  change (2^k) • halfDifference n hn T.val σ=0
  rw [←actual_difference_nsmul,hk,halfDifference,map_zero,sub_zero]

def primaryBoundaryHom (n : F) (hn : n ≠ 0) : geometricPrimary n →+ primaryCocycles n hn where
  toFun := primaryBoundary n hn
  map_zero' := Subtype.ext (map_zero (fullBoundaryHom n hn))
  map_add' T U := Subtype.ext (actual_full_boundary_add n hn T.val U.val)

/-- Actual continuous primary H1, with the genuine crossed action and actual primary coboundaries. -/
abbrev continuousPrimaryHOne (n : F) (hn : n ≠ 0) := primaryCocycles n hn ⧸ (primaryBoundaryHom n hn).range

def primaryClass (n : F) (hn : n ≠ 0) : primaryCocycles n hn →+ continuousPrimaryHOne n hn := QuotientAddGroup.mk' _

end ActualTwoDescentPrimaryGeometricBoundary318
