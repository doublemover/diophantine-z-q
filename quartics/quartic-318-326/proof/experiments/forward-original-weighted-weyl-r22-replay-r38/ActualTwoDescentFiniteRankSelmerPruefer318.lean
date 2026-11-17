module
public import ActualTwoDescentFiniteRankPrimarySelmerEquivalence318
public section
noncomputable section
namespace ActualTwoDescentFiniteRankSelmerPruefer318
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
open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentHigherKummerHom318
open ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318
open ActualTwoDescentPrimaryGeometricBoundary318 ActualTwoDescentFiniteLevelIntoPrimary318
open ActualTwoDescentPrimaryFullClass318 ActualTwoDescentActualPrimarySelmer318
open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherSelmerIntoPrimary318
open ActualTwoDescentPrimarySelmerFiniteLevels318 ActualTwoDescentHigherRationalImage318

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaReducedDuality318
open ActualTwoDescentActualShaZeroPrueferDuality318 ActualTwoDescentActualShaPrimaryVanishing318
open ActualTwoDescentActualShaRankAlternative318 ActualTwoDescentFiniteRankPrimarySelmerEquivalence318
open ActualTwoDescentDyadicPrueferModel318 ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- Genuine corank-one Prüfer identification of actual full primary Selmer in the finite rational-point branch, conditional on genuine global duality. This does NOT assert the finite rational-point branch holds. -/
theorem actual_finite_rank_selmer_pruefer (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (hdual : ActualReducedDuality n hn) [Finite (Point n)] :
    Nonempty (actualPrimarySelmer n hn ≃+ Additive PrueferTwo) := by
  rcases actual_sha_zero_or_pruefer_of_duality n hn hf hb hS hdual with hz|⟨hi,⟨e⟩⟩
  · have htwo := actual_sha_two_one_of_primary_trivial n hn hz
    haveI : Infinite (Point n) := (actual_sha_one_iff_infinite n hn hf hb hS).mp htwo
    exact (not_finite (Point n)).elim
  · let ea : Additive (actualShaPrimary n hn) ≃+ Additive PrueferTwo :=
      { toEquiv := e.toEquiv
        map_add' x y := e.map_mul x.toMul y.toMul }
    exact ⟨(finiteRankPrimarySelmerEquiv n hn).trans ea⟩

end ActualTwoDescentFiniteRankSelmerPruefer318
