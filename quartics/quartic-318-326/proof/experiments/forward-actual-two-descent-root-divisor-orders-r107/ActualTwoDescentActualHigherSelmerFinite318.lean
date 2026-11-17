module
public import ActualTwoDescentHigherRationalQuotientFinite318
public section
noncomputable section
namespace ActualTwoDescentActualHigherSelmerFinite318
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

open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentActualShaPower318 ActualTwoDescentActualShaPowerBounds318
open ActualTwoDescentHigherSelmerCardinality318 ActualTwoDescentHigherRationalQuotientFinite318
open ActualTwoDescentHigherMultiplesTransport318 ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- Finiteness of the actual independently defined higher Selmer group is now proved, not inferred merely from a formal cardinal product. -/
theorem actual_higher_selmer_finite (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (k : ℕ) : Finite (actualHigherSelmer n hn k) := by
  letI := actual_higher_rational_quotient_finite n hn hf k
  letI := (actual_sha_power_finite_bound n hn hf hb hS k).1
  apply Nat.finite_of_card_ne_zero
  rw [←actual_higher_selmer_card_product]
  exact (mul_pos Nat.card_pos Nat.card_pos).ne'

end ActualTwoDescentActualHigherSelmerFinite318
