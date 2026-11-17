module
public import ActualTwoDescentTrivialShaPowerCard318
public section
noncomputable section
namespace ActualTwoDescentActualShaPowerCorank318
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

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaPower318 ActualTwoDescentActualShaPowerBounds318
open ActualTwoDescentTrivialShaPowerCard318 ActualTwoDescentDyadicPrueferModel318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- Actual zero/Prüfer identification gives exact higher torsion growth at every k. -/
lemma actual_sha_power_corank_formula (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (t : ℕ)
    (ht : (t=0 ∧ Subsingleton (actualShaPrimary n hn)) ∨
      (t=1 ∧ Nonempty (actualShaPrimary n hn ≃* PrueferTwo))) (k : ℕ) :
    Nat.card (actualShaPower n hn k)=2^(k*t) := by
  rcases ht with ⟨rfl,hz⟩|⟨rfl,⟨e⟩⟩
  · simpa only [mul_zero,pow_zero] using actual_trivial_sha_power_card n hn hz k
  · letI := actual_pruefer_infinite
    haveI : Infinite (actualShaPrimary n hn) := Infinite.of_injective e.symm e.symm.injective
    simpa only [mul_one] using actual_infinite_sha_power_card n hn hf hb hS k

end ActualTwoDescentActualShaPowerCorank318
