module
public import ActualTwoDescentJointCyclicPrimaryInvolutions318
public section
noncomputable section
namespace ActualTwoDescentRationalPrimaryTwoBound318
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

open ActualTwoDescentPrimaryPowerLevels318

lemma actual_rational_primary_is_two_group (n : ℚ) (hn : n ≠ 0) :
    IsPGroup 2 (Multiplicative (rationalPrimaryImage n hn)) := by
  intro x
  obtain ⟨k,hk⟩ := actual_primary_selmer_two_primary n hn x.toAdd.val
  exact ⟨k,Subtype.ext hk⟩

lemma actual_rank_one_rational_two_bound (n : ℚ) (hn : n ≠ 0)
    {T : Type} [AddCommGroup T] [Finite T] (e : Point n ≃+ ℤ × T) :
    Finite (powerLevel (Multiplicative (rationalPrimaryImage n hn)) 1) ∧
      Nat.card (powerLevel (Multiplicative (rationalPrimaryImage n hn)) 1) ≤ 2 := by
  apply actual_joint_cyclic_primary_two_bound (actual_rational_primary_is_two_group n hn)
  intro x y
  obtain ⟨g,⟨a,ha⟩,⟨b,hb⟩⟩ := actual_rank_one_primary_joint_cyclic n hn e x.toAdd y.toAdd
  exact ⟨Multiplicative.ofAdd g,⟨a,congrArg Multiplicative.ofAdd ha⟩,
    ⟨b,congrArg Multiplicative.ofAdd hb⟩⟩

end ActualTwoDescentRationalPrimaryTwoBound318
