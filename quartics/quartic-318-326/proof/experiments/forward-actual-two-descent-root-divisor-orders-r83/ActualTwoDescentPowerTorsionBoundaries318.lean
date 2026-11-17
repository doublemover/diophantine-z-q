module
public import ActualTwoDescentPowerCocycleRepresentation318
public section
noncomputable section
namespace ActualTwoDescentPowerTorsionBoundaries318
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

open ActualTwoDescentGeometricPowerTorsion318 ActualTwoDescentPowerValuedCocycles318 ActualTwoDescentFullBoundaryHom318

def powerBoundary (n : F) (hn : n ≠ 0) (k : ℕ) (T : geometricPowerTorsion n k) : powerValuedCocycles n hn k := by
  refine ⟨fullBoundary n hn T.val,?_⟩
  intro σ
  change (2^k) • halfDifference n hn T.val σ=0
  rw [←actual_difference_nsmul]
  have h : (2^k) • T.val=0 := T.property
  rw [h,halfDifference,map_zero,sub_zero]

def powerBoundaryHom (n : F) (hn : n ≠ 0) (k : ℕ) : geometricPowerTorsion n k →+ powerValuedCocycles n hn k where
  toFun := powerBoundary n hn k
  map_zero' := Subtype.ext (map_zero (fullBoundaryHom n hn))
  map_add' T U := Subtype.ext (actual_full_boundary_add n hn T.val U.val)

/-- Actual continuous first cohomology: crossed cocycles modulo boundaries of ACTUAL E[2^k] points. -/
abbrev continuousPowerHOne (n : F) (hn : n ≠ 0) (k : ℕ) :=
  powerValuedCocycles n hn k ⧸ (powerBoundaryHom n hn k).range

def powerClass (n : F) (hn : n ≠ 0) (k : ℕ) : powerValuedCocycles n hn k →+ continuousPowerHOne n hn k :=
  QuotientAddGroup.mk' _

end ActualTwoDescentPowerTorsionBoundaries318
