module
public import ActualTwoDescentFiniteRationalPrimaryVanishing318
public section
noncomputable section
namespace ActualTwoDescentFiniteRankPrimarySelmerEquivalence318
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

open ActualTwoDescentActualPrimaryRationalImage318 ActualTwoDescentPrimarySelmerToSha318
open ActualTwoDescentPrimarySelmerShaKernel318 ActualTwoDescentPrimarySelmerShaSurjectivity318
open ActualTwoDescentFiniteRationalPrimaryVanishing318 ActualTwoDescentActualShaPrimary318

lemma actual_finite_rank_primary_selmer_injective (n : ℚ) (hn : n ≠ 0) [Finite (Point n)] :
    Function.Injective (primarySelmerToSha n hn) := by
  letI := actual_finite_rational_primary_zero n hn
  intro x y h
  apply sub_eq_zero.mp
  have hm : x-y ∈ rationalPrimaryImage n hn := by
    rw [←actual_primary_selmer_sha_kernel]
    change primarySelmerToSha n hn (x-y)=0
    rw [map_sub,h,sub_self]
  exact congrArg Subtype.val (Subsingleton.elim (⟨x-y,hm⟩ : rationalPrimaryImage n hn) 0)

/-- In the actual rank-zero branch, full primary Selmer is explicitly isomorphic to ACTUAL full primary Sha. -/
def finiteRankPrimarySelmerEquiv (n : ℚ) (hn : n ≠ 0) [Finite (Point n)] :
    actualPrimarySelmer n hn ≃+ Additive (actualShaPrimary n hn) :=
  AddEquiv.ofBijective (primarySelmerToSha n hn) ⟨actual_finite_rank_primary_selmer_injective n hn,
    actual_primary_selmer_sha_surjective n hn⟩

end ActualTwoDescentFiniteRankPrimarySelmerEquivalence318
