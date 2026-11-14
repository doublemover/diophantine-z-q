module
public import ActualTwoDescentHigherCohomologyDirectedMaps318
public import Mathlib.Algebra.Colimit.DirectLimit
public section
noncomputable section
namespace ActualTwoDescentHigherCohomologyDirectedSystem318
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

open ActualTwoDescentHigherCohomologyDirectedMaps318 ActualTwoDescentFiniteLevelIntoPrimary318

instance actual_higher_cohomology_directed (n : F) (hn : n ≠ 0) :
    DirectedSystem (fun k => continuousPowerHOne n hn k) (fun i j h => higherCohomologyMap n hn i j h) where
  map_self x := by obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x; rfl
  map_map hij hjk x := by obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x; rfl

lemma actual_power_primary_compatible (n : F) (hn : n ≠ 0) (i j : ℕ) (h : i ≤ j) (x : continuousPowerHOne n hn i) :
    powerIntoPrimaryHOne n hn j (higherCohomologyMap n hn i j h x)=powerIntoPrimaryHOne n hn i x := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x
  rfl

end ActualTwoDescentHigherCohomologyDirectedSystem318
