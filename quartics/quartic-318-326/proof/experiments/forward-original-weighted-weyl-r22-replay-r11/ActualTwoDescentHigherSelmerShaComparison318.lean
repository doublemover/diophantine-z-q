module
public import ActualTwoDescentActualHigherSelmer318
public section
noncomputable section
namespace ActualTwoDescentHigherSelmerShaComparison318
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

open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherLocalConditions318
open ActualTwoDescentHigherCohomologyRestriction318 ActualTwoDescentActualShaDefinition318
open ActualTwoDescentShaRepresentativeIndependence318

lemma actual_higher_selmer_representative (n : ℚ) (hn : n ≠ 0) (k : ℕ)
    (z : powerValuedCocycles n hn k) :
    powerClass n hn k z ∈ actualHigherSelmer n hn k ↔ EverywhereLocallyTrivial n hn z.val := by
  change (_ ∧ ∀ (p : ℕ) [Fact p.Prime], _) ↔ _
  simp only [actual_higher_local_condition_iff,actual_higher_restriction_full,EverywhereLocallyTrivial]

/-- Independent actual local-image conditions identify exactly the preimage of the ACTUAL Sha subgroup under the actual full-H1 map. -/
theorem actual_higher_selmer_iff_sha (n : ℚ) (hn : n ≠ 0) (k : ℕ) (x : continuousPowerHOne n hn k) :
    x ∈ actualHigherSelmer n hn k ↔ higherFullClass n hn k x ∈ actualSha n hn := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [actual_higher_selmer_representative]
  exact (actual_sha_class_iff n hn z.val).symm

end ActualTwoDescentHigherSelmerShaComparison318
