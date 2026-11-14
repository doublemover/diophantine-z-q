module
public import ActualTwoDescentPrimaryFiniteLevelSurjectivity318
public section
noncomputable section
namespace ActualTwoDescentHigherCohomologyDirectedMaps318
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

def powerTorsionMap (n : F) (i j : ℕ) (h : i ≤ j) : geometricPowerTorsion n i →+ geometricPowerTorsion n j where
  toFun T := ⟨T.val,actual_nsmul_power_mono h T.property⟩
  map_zero' := rfl
  map_add' T U := rfl

def powerCocycleMap (n : F) (hn : n ≠ 0) (i j : ℕ) (h : i ≤ j) : powerValuedCocycles n hn i →+ powerValuedCocycles n hn j where
  toFun z := ⟨z.val,fun σ => actual_nsmul_power_mono h (z.property σ)⟩
  map_zero' := rfl
  map_add' z w := rfl

def higherCohomologyMap (n : F) (hn : n ≠ 0) (i j : ℕ) (h : i ≤ j) : continuousPowerHOne n hn i →+ continuousPowerHOne n hn j :=
  QuotientAddGroup.lift _ ((powerClass n hn j).comp (powerCocycleMap n hn i j h)) (by
    rintro z ⟨T,rfl⟩
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨powerTorsionMap n i j h T,rfl⟩)

lemma actual_higher_map_full_class (n : F) (hn : n ≠ 0) (i j : ℕ) (h : i ≤ j) (x : continuousPowerHOne n hn i) :
    higherFullClass n hn j (higherCohomologyMap n hn i j h x)=higherFullClass n hn i x := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x
  rfl

end ActualTwoDescentHigherCohomologyDirectedMaps318
