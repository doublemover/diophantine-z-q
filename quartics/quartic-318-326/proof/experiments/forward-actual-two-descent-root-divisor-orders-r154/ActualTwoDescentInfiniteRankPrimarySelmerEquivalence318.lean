module
public import ActualTwoDescentInfiniteRationalRankOneDecomposition318
public section
noncomputable section
namespace ActualTwoDescentInfiniteRankPrimarySelmerEquivalence318
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
open ActualTwoDescentRankOneRationalPruefer318
open ActualTwoDescentInfiniteRationalRankOneDecomposition318

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaPrimaryVanishing318
open ActualTwoDescentActualShaRankAlternative318 ActualTwoDescentPrimarySelmerToSha318
open ActualTwoDescentPrimarySelmerShaKernel318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentAllPlacesIntersection318

lemma actual_infinite_primary_image_surjective (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) [Infinite (Point n)] :
    Function.Surjective (rationalPrimaryImage n hn).subtype := by
  haveI := actual_sha_primary_trivial_of_sha_two_one n hn
    ((actual_sha_one_iff_infinite n hn hf hb hS).mpr inferInstance)
  intro x
  have hx : x ∈ (primarySelmerToSha n hn).ker := Subsingleton.elim _ _
  rw [actual_primary_selmer_sha_kernel] at hx
  exact ⟨⟨x,hx⟩,rfl⟩

def infiniteRankPrimarySelmerEquiv (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) [Infinite (Point n)] :
    actualPrimarySelmer n hn ≃+ rationalPrimaryImage n hn :=
  (AddEquiv.ofBijective (rationalPrimaryImage n hn).subtype
    ⟨Subtype.val_injective,actual_infinite_primary_image_surjective n hn hf hb hS⟩).symm

end ActualTwoDescentInfiniteRankPrimarySelmerEquivalence318
