module
public import ActualTwoDescentPowerTorsionRestriction318
public section
noncomputable section
namespace ActualTwoDescentHigherCohomologyRestriction318
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

open ActualTwoDescentPowerTorsionRestriction318

/-- Actual closure embedding and native Galois restriction descend to continuous higher cohomology. -/
def higherRestriction (f : F →+* L) (n : F) (hn : n ≠ 0) (k : ℕ) :
    continuousPowerHOne n hn k →+ continuousPowerHOne (f n) (field_map_ne_zero f hn) k :=
  QuotientAddGroup.lift _ ((powerClass (f n) (field_map_ne_zero f hn) k).comp (powerCocycleRestriction f n hn k)) (by
    rintro z ⟨T,rfl⟩
    change powerClass _ _ _ (powerCocycleRestriction f n hn k (powerBoundaryHom n hn k T))=0
    rw [actual_power_restriction_boundary]
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨powerTorsionTransport f n hn k T,rfl⟩)

lemma actual_higher_restriction_full (f : F →+* L) (n : F) (hn : n ≠ 0) (k : ℕ)
    (z : powerValuedCocycles n hn k) :
    higherFullClass (f n) (field_map_ne_zero f hn) k (higherRestriction f n hn k (powerClass n hn k z))=
      fullClassHom (f n) (field_map_ne_zero f hn) (fullCocycleRestriction f n hn z.val) := rfl

end ActualTwoDescentHigherCohomologyRestriction318
