module
public import ActualTwoDescentHigherRationalQuotient318
public section
noncomputable section
namespace ActualTwoDescentHigherSelmerCardinality318
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
open ActualTwoDescentHigherSelmerShaEquivalence318 ActualTwoDescentActualShaPower318 ActualTwoDescentHigherRationalQuotient318

/-- Exact cardinal identity at EVERY higher Selmer level, without assuming finiteness to conceal a missing construction. -/
theorem actual_higher_selmer_card_product (n : ℚ) (hn : n ≠ 0) (k : ℕ) :
    Nat.card (Point n ⧸ (nsmulAddMonoidHom (Point n) (2^k)).range)*Nat.card (actualShaPower n hn k)=
      Nat.card (actualHigherSelmer n hn k) := by
  rw [Nat.card_congr (higherRationalQuotientEquiv n hn k).toEquiv,
    ←Nat.card_congr (higherSelmerShaEquiv n hn k).toEquiv]
  exact ((higherRationalHom n hn k).range).card_mul_index

end ActualTwoDescentHigherSelmerCardinality318
