module
public import ActualTwoDescentActualShaPowerCorank318
public section
noncomputable section
namespace ActualTwoDescentActualSelmerGrowthFormula318
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

open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherSelmerCardinality318
open ActualTwoDescentHigherFreeFiniteIndex318 ActualTwoDescentHigherMultiplesTransport318
open ActualTwoDescentActualShaPowerCorank318 ActualTwoDescentActualShaPrimary318 ActualTwoDescentDyadicPrueferModel318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

lemma actual_selmer_growth_from_decomposition (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (r t : ℕ)
    (T : Type) [AddCommGroup T] [Finite T] (e : Point n ≃+ (Fin r →₀ ℤ) × T)
    (ht : (t=0 ∧ Subsingleton (actualShaPrimary n hn)) ∨
      (t=1 ∧ Nonempty (actualShaPrimary n hn ≃* PrueferTwo))) (k : ℕ) :
    Nat.card (actualHigherSelmer n hn k)=Nat.card (torsionKernel T (2^k))*2^(k*(r+t)) := by
  rw [←actual_higher_selmer_card_product,actual_higher_free_finite_index r T e,
    actual_sha_power_corank_formula n hn hf hb hS t ht]
  calc
    (2^k)^r*Nat.card (torsionKernel T (2^k))*2^(k*t)=
        Nat.card (torsionKernel T (2^k))*((2^k)^r*2^(k*t)) := by ring
    _=Nat.card (torsionKernel T (2^k))*2^(k*(r+t)) := by rw [←pow_mul,←pow_add,←Nat.mul_add]

end ActualTwoDescentActualSelmerGrowthFormula318
