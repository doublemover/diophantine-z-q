module
public import ActualTwoDescentHigherSelmerShaEquivalence318
public section
noncomputable section
namespace ActualTwoDescentHigherRationalQuotient318
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

open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherRationalImage318
open ActualTwoDescentHigherKummerKernelReverse318

lemma actual_higher_rational_kernel (n : ℚ) (hn : n ≠ 0) (k : ℕ) :
    (higherRationalHom n hn k).ker=(nsmulAddMonoidHom (Point n) (2^k)).range := by
  ext P
  change higherRationalHom n hn k P=0 ↔ _
  constructor
  · intro h
    exact (actual_higher_kummer_kernel n hn k P).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((actual_higher_kummer_kernel n hn k P).mpr h)

/-- Actual rational Kummer image has EXACTLY the genuine higher rational quotient, not merely a cardinality bound. -/
def higherRationalQuotientEquiv (n : ℚ) (hn : n ≠ 0) (k : ℕ) :
    Point n ⧸ (nsmulAddMonoidHom (Point n) (2^k)).range ≃+ (higherRationalHom n hn k).range := by
  have e := QuotientAddGroup.quotientKerEquivRange (higherRationalHom n hn k)
  rw [actual_higher_rational_kernel] at e
  exact e

end ActualTwoDescentHigherRationalQuotient318
