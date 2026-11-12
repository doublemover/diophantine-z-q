module
public import ActualTwoDescentRestrictedRationalPrimaryDivision318
public section
noncomputable section
namespace ActualTwoDescentFiniteFactorPrimaryVanishing318
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

/-- Every actual finite Mordell-Weil factor vanishes in the genuine primary image.
The roots stay in the restricted image of this SAME factor. -/
lemma actual_finite_factor_primary_zero (n : ℚ) (hn : n ≠ 0)
    {T : Type} [AddCommGroup T] [Finite T] (f : T →+ Point n) (k : ℕ) (t : T) :
    rationalPrimaryHom n hn k (f t)=0 := by
  have hz (y : restrictedRationalPrimaryImage n hn f) : Nat.card T • y=0 := by
    obtain ⟨i,u,hu⟩ := y.property
    apply Subtype.ext
    change Nat.card T • y.val=0
    rw [←hu,←map_nsmul,←map_nsmul,card_nsmul_eq_zero',map_zero,map_zero]
  let x : restrictedRationalPrimaryImage n hn f := ⟨rationalPrimaryHom n hn k (f t),⟨k,t,rfl⟩⟩
  obtain ⟨y,hy⟩ := actual_restricted_primary_all_surjective n hn f (Nat.card T) Nat.card_pos.ne' x
  exact congrArg Subtype.val (hy.symm.trans (hz y))

end ActualTwoDescentFiniteFactorPrimaryVanishing318
