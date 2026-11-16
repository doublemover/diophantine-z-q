module
public import ActualTwoDescentHigherLocalConditions318
public section
noncomputable section
namespace ActualTwoDescentActualHigherSelmer318
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

open ActualTwoDescentHigherCohomologyRestriction318 ActualTwoDescentHigherLocalConditions318

/-- Genuine higher Selmer group: actual higher continuous cohomology classes whose actual restrictions lie in actual local rational Kummer images at EVERY place. -/
def actualHigherSelmer (n : ℚ) (hn : n ≠ 0) (k : ℕ) : AddSubgroup (continuousPowerHOne n hn k) where
  carrier := {x | higherLocalCondition (algebraMap ℚ ℝ) n hn k x ∧
    ∀ (p : ℕ) [Fact p.Prime], higherLocalCondition (algebraMap ℚ (ℚ_[p])) n hn k x}
  zero_mem' := by
    constructor
    · change higherRestriction _ _ _ _ 0 ∈ _
      rw [map_zero]; exact AddSubgroup.zero_mem _
    · intro p _
      change higherRestriction _ _ _ _ 0 ∈ _
      rw [map_zero]; exact AddSubgroup.zero_mem _
  add_mem' := by
    rintro x y ⟨hxR,hxp⟩ ⟨hyR,hyp⟩
    constructor
    · change higherRestriction _ _ _ _ (x+y) ∈ _
      rw [map_add]; exact AddSubgroup.add_mem _ hxR hyR
    · intro p _
      change higherRestriction _ _ _ _ (x+y) ∈ _
      rw [map_add]; exact AddSubgroup.add_mem _ (hxp p) (hyp p)
  neg_mem' := by
    rintro x ⟨hxR,hxp⟩
    constructor
    · change higherRestriction _ _ _ _ (-x) ∈ _
      rw [map_neg]; exact AddSubgroup.neg_mem _ hxR
    · intro p _
      change higherRestriction _ _ _ _ (-x) ∈ _
      rw [map_neg]; exact AddSubgroup.neg_mem _ (hxp p)

end ActualTwoDescentActualHigherSelmer318
