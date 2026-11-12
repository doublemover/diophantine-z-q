module
public import ActualTwoDescentActualRankShaCorankEquation318
public section
noncomputable section
namespace ActualTwoDescentGeometricDivisionTower318
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

/-- Actual compatible geometric division points on the original elliptic curve. -/
def geometricDivision (n : F) (hn : n ≠ 0) (P : Point (algebraMap F Qbar n)) : ℕ → Point (algebraMap F Qbar n)
  | 0 => P
  | k+1 => actualHalf n hn (geometricDivision n hn P k)

lemma actual_geometric_division_step (n : F) (hn : n ≠ 0) (P) (k : ℕ) :
    2 • geometricDivision n hn P (k+1)=geometricDivision n hn P k := by
  change 2 • actualHalf n hn (geometricDivision n hn P k)=_
  rw [two_nsmul,actual_half_spec]

lemma actual_geometric_division_power (n : F) (hn : n ≠ 0) (P) (k : ℕ) :
    (2^k) • geometricDivision n hn P k=P := by
  induction k with
  | zero => simp [geometricDivision]
  | succ k ih => rw [pow_succ,mul_smul,actual_geometric_division_step,ih]

end ActualTwoDescentGeometricDivisionTower318
