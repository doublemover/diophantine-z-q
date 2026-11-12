module
public import ActualTwoDescentRationalPrimaryTwoBound318
public section
noncomputable section
namespace ActualTwoDescentRankOnePrimaryNonzero318
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

open ActualTwoDescentPrimaryClassEventualEquality318 ActualTwoDescentHigherCohomologyDirectedMaps318
open ActualTwoDescentHigherKummerKernelForward318

lemma actual_rank_one_generator_primary_nonzero (n : ℚ) (hn : n ≠ 0)
    {T : Type} [AddCommGroup T] (e : Point n ≃+ ℤ × T) :
    rationalPrimaryHom n hn 1 (rankOneGenerator n e) ≠ 0 := by
  intro hz
  have hz' : powerIntoPrimaryHOne n hn 1 (higherKummerHom n hn 1 (rankOneGenerator n e))=0 :=
    congrArg Subtype.val hz
  obtain ⟨j,hj,hzero⟩ := actual_primary_class_eventual_zero n hn 1 _ hz'
  rw [actual_higher_kummer_directed] at hzero
  obtain ⟨Q,hQ⟩ := actual_higher_kummer_zero_implies_divisible n hn j _ hzero
  have he := congrArg (fun P : Point n => (e P).1) hQ
  have he' : (2^j : ℤ)*(e Q).1=2^(j-1) := by
    simpa [rankOneGenerator,map_nsmul,nsmul_eq_mul] using he
  have hp : (2^j : ℤ)=2^(j-1)*2 := by
    rw [←pow_succ,show j-1+1=j from Nat.sub_add_cancel hj]
  rw [hp,mul_assoc] at he'
  have hnz : (2^(j-1) : ℤ) ≠ 0 := pow_ne_zero _ (by decide)
  have heq : (2 : ℤ)*(e Q).1=1 := mul_left_cancel₀ hnz (by simpa using he')
  omega

end ActualTwoDescentRankOnePrimaryNonzero318
