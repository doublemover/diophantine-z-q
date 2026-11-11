module
public import ActualTwoDescentHigherCohomologyRestriction318
public section
noncomputable section
namespace ActualTwoDescentHigherLocalConditions318
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
open ActualTwoDescentHigherKummerHom318 ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318
open ActualTwoDescentHigherFullLifting318 ActualTwoDescentGeometricPowerTorsion318
open ActualTwoDescentFullCocycleRestriction318 ActualTwoDescentGeometricPointTransport318
open ActualTwoDescentSquareClassFieldMap318
variable {L : Type} [Field L] [CharZero L] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

open ActualTwoDescentHigherCohomologyRestriction318

/-- Actual local Kummer image, defined before and independently of the global Sha subgroup. -/
def higherLocalCondition (f : F →+* L) (n : F) (hn : n ≠ 0) (k : ℕ)
    (x : continuousPowerHOne n hn k) : Prop :=
  higherRestriction f n hn k x ∈ (higherKummerHom (f n) (field_map_ne_zero f hn) k).range

lemma actual_higher_local_condition_iff (f : F →+* L) (n : F) (hn : n ≠ 0) (k : ℕ)
    (x : continuousPowerHOne n hn k) :
    higherLocalCondition f n hn k x ↔ higherFullClass (f n) (field_map_ne_zero f hn) k (higherRestriction f n hn k x)=0 :=
  (actual_higher_full_kernel (f n) (field_map_ne_zero f hn) k _).symm

end ActualTwoDescentHigherLocalConditions318
