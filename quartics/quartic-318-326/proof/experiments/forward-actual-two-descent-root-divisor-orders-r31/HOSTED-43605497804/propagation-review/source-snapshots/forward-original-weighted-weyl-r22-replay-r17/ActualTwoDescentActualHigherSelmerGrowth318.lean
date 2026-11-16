module
public import ActualTwoDescentActualSelmerGrowthFormula318
public section
noncomputable section
namespace ActualTwoDescentActualHigherSelmerGrowth318
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

open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentActualHigherSelmerFinite318
open ActualTwoDescentActualShaReducedDuality318 ActualTwoDescentActualRankShaCorankEquation318
open ActualTwoDescentActualSelmerGrowthFormula318 ActualTwoDescentFiniteTorsionStabilization318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- Genuine all-place higher Selmer groups have eventually EXACT C*2^k order, conditional on the still-missing global reduced duality pairing. No analytic or rational-rank branch is selected. -/
theorem actual_higher_selmer_eventual_growth (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (hdual : ActualReducedDuality n hn) :
    (∀ k : ℕ, Finite (actualHigherSelmer n hn k)) ∧
    ∃ N C : ℕ, 0<C ∧ ∀ k, N ≤ k → Nat.card (actualHigherSelmer n hn k)=C*2^k := by
  refine ⟨actual_higher_selmer_finite n hn hf hb hS,?_⟩
  obtain ⟨r,t,hrt,T,hT,hfin,⟨e⟩,ht⟩ := actual_free_rank_plus_sha_corank n hn hf hb hS hdual
  letI := hT
  letI := hfin
  obtain ⟨N,C,hC,hN⟩ := actual_finite_torsion_stabilizes T
  refine ⟨N,C,hC,?_⟩
  intro k hk
  rw [actual_selmer_growth_from_decomposition n hn hf hb hS r t T e ht k,hN k hk,hrt,mul_one]

end ActualTwoDescentActualHigherSelmerGrowth318
