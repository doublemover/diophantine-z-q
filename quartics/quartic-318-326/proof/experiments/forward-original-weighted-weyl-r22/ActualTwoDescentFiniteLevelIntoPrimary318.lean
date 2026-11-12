module
public import ActualTwoDescentPrimaryGeometricBoundary318
public section
noncomputable section
namespace ActualTwoDescentFiniteLevelIntoPrimary318
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

def powerIntoPrimaryCocycles (n : F) (hn : n ≠ 0) (k : ℕ) : powerValuedCocycles n hn k →+ primaryCocycles n hn where
  toFun z := ⟨z.val,fun σ => ⟨k,z.property σ⟩⟩
  map_zero' := rfl
  map_add' z w := rfl

def powerIntoPrimaryHOne (n : F) (hn : n ≠ 0) (k : ℕ) : continuousPowerHOne n hn k →+ continuousPrimaryHOne n hn :=
  QuotientAddGroup.lift _ ((primaryClass n hn).comp (powerIntoPrimaryCocycles n hn k)) (by
    rintro z ⟨T,rfl⟩
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨⟨T.val,⟨k,T.property⟩⟩,rfl⟩)

end ActualTwoDescentFiniteLevelIntoPrimary318
