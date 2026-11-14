module
public import ActualTwoDescentRankOnePrimaryNonzero318
public section
noncomputable section
namespace ActualTwoDescentRankOnePrimaryInfinite318
set_option maxHeartbeats 16000000
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

open ActualTwoDescentActualPrimaryRationalImage318 ActualTwoDescentRationalPrimaryDivision318
open ActualTwoDescentFullPrimarySelmerTorsion318 ActualTwoDescentPrimaryAllRoots318


open ActualTwoDescentPrimaryAllRoots318 ActualTwoDescentFullPrimarySelmerTorsion318

open ActualTwoDescentRestrictedRationalPrimaryImage318
open ActualTwoDescentRestrictedRationalPrimaryDivision318
open ActualTwoDescentFiniteFactorPrimaryVanishing318
open ActualTwoDescentRankOneRationalCoordinates318
open ActualTwoDescentRankOnePrimaryJointCyclic318
open ActualTwoDescentJointCyclicPrimaryInvolutions318
open ActualTwoDescentRationalPrimaryTwoBound318
open ActualTwoDescentRankOnePrimaryNonzero318

lemma actual_rank_one_rational_primary_infinite (n : ℚ) (hn : n ≠ 0)
    {T : Type} [AddCommGroup T] (e : Point n ≃+ ℤ × T) : Infinite (rationalPrimaryImage n hn) := by
  classical
  by_contra h
  letI : Finite (rationalPrimaryImage n hn) := by
    by_contra hfin
    exact h (not_finite_iff_infinite.mp hfin)
  let x : rationalPrimaryImage n hn :=
    ⟨rationalPrimaryHom n hn 1 (rankOneGenerator n e),⟨1,rankOneGenerator n e,rfl⟩⟩
  obtain ⟨y,hy⟩ := actual_rational_primary_all_surjective n hn
    (Nat.card (rationalPrimaryImage n hn)) Nat.card_pos.ne' x
  have hx : x=0 := hy.symm.trans (card_nsmul_eq_zero' y)
  exact actual_rank_one_generator_primary_nonzero n hn e (congrArg Subtype.val hx)

end ActualTwoDescentRankOnePrimaryInfinite318
