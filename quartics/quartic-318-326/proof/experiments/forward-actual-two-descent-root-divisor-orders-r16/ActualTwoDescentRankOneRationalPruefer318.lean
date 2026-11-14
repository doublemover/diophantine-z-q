module
public import ActualTwoDescentRankOnePrimaryInfinite318
public section
noncomputable section
namespace ActualTwoDescentRankOneRationalPruefer318
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
open ActualTwoDescentRankOnePrimaryInfinite318

open ActualTwoDescentPrueferClassification318 ActualTwoDescentDyadicPrueferModel318

/-- Genuine rank-one rational primary Kummer image, not a formal quotient designated Prüfer. -/
theorem actual_rank_one_rational_pruefer (n : ℚ) (hn : n ≠ 0)
    {T : Type} [AddCommGroup T] [Finite T] (e : Point n ≃+ ℤ × T) :
    Nonempty (rationalPrimaryImage n hn ≃+ Additive PrueferTwo) := by
  letI := actual_rank_one_rational_primary_infinite n hn e
  obtain ⟨ht,hc⟩ := actual_rank_one_rational_two_bound n hn e
  obtain ⟨a⟩ := actual_infinite_primary_pruefer (actual_rational_primary_is_two_group n hn) ht hc
  exact ⟨{ toEquiv := { toFun := fun x => Additive.ofMul (a (Multiplicative.ofAdd x))
                       invFun := fun y => (a.symm y.toMul).toAdd
                       left_inv := fun x => congrArg Multiplicative.toAdd (a.left_inv (Multiplicative.ofAdd x))
                       right_inv := fun y => congrArg Additive.ofMul (a.right_inv y.toMul) }
           map_add' x y := congrArg Additive.ofMul (a.map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)) }⟩

end ActualTwoDescentRankOneRationalPruefer318
