module
public import ActualTwoDescentRankOneRationalCoordinates318
public section
noncomputable section
namespace ActualTwoDescentRankOnePrimaryJointCyclic318
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

/-- Two actual rational primary classes share one cyclic finite-level generator.
The common level retains BOTH transition multipliers. -/
lemma actual_rank_one_primary_joint_cyclic (n : ℚ) (hn : n ≠ 0)
    {T : Type} [AddCommGroup T] [Finite T] (e : Point n ≃+ ℤ × T)
    (x y : rationalPrimaryImage n hn) :
    ∃ g : rationalPrimaryImage n hn, x ∈ AddSubgroup.zmultiples g ∧ y ∈ AddSubgroup.zmultiples g := by
  obtain ⟨i,P,hP⟩ := x.property
  obtain ⟨j,Q,hQ⟩ := y.property
  let k := max i j
  let g : rationalPrimaryImage n hn :=
    ⟨rationalPrimaryHom n hn k (rankOneGenerator n e),⟨k,rankOneGenerator n e,rfl⟩⟩
  refine ⟨g,?_,?_⟩
  · refine ⟨(e ((2^(k-i)) • P)).1,?_⟩
    apply Subtype.ext
    change _=x.val
    rw [←actual_rank_one_primary_coordinate n hn e,
      ←actual_rational_primary_transition n hn i k (le_max_left i j),hP]
  · refine ⟨(e ((2^(k-j)) • Q)).1,?_⟩
    apply Subtype.ext
    change _=y.val
    rw [←actual_rank_one_primary_coordinate n hn e,
      ←actual_rational_primary_transition n hn j k (le_max_right i j),hQ]

end ActualTwoDescentRankOnePrimaryJointCyclic318
