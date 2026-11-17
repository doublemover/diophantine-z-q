module
public import ActualTwoDescentHigherSelmerShaComparison318
public section
noncomputable section
namespace ActualTwoDescentActualShaPower318
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

open ActualTwoDescentActualShaDefinition318

/-- Actual2^k-torsion of full elliptic Sha, defined without using a Selmer quotient. -/
def actualShaPower (n : ℚ) (hn : n ≠ 0) (k : ℕ) : AddSubgroup (H1 (fullEllipticRep n hn)) where
  carrier := {x | x ∈ actualSha n hn ∧ (2^k) • x=0}
  zero_mem' := ⟨(actualSha n hn).zero_mem,nsmul_zero _⟩
  add_mem' := by
    rintro x y ⟨hx,hxk⟩ ⟨hy,hyk⟩
    exact ⟨(actualSha n hn).add_mem hx hy,by rw [nsmul_add,hxk,hyk,zero_add]⟩
  neg_mem' := by
    rintro x ⟨hx,hxk⟩
    exact ⟨(actualSha n hn).neg_mem hx,by rw [nsmul_neg,hxk,neg_zero]⟩

end ActualTwoDescentActualShaPower318
