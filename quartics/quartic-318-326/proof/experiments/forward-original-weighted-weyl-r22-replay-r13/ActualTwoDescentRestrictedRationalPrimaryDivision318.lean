module
public import ActualTwoDescentRestrictedRationalPrimaryImage318
public section
noncomputable section
namespace ActualTwoDescentRestrictedRationalPrimaryDivision318
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

lemma actual_restricted_primary_two_surjective (n : ℚ) (hn : n ≠ 0)
    {T : Type} [AddCommGroup T] (f : T →+ Point n) :
    Function.Surjective (nsmulAddMonoidHom (α:=restrictedRationalPrimaryImage n hn f) 2) := by
  rintro ⟨x,k,t,rfl⟩
  exact ⟨⟨rationalPrimaryHom n hn (k+1) (f t),⟨k+1,t,rfl⟩⟩,
    Subtype.ext (actual_rational_primary_half n hn k (f t))⟩

lemma actual_restricted_primary_all_surjective (n : ℚ) (hn : n ≠ 0)
    {T : Type} [AddCommGroup T] (f : T →+ Point n) (m : ℕ) (hm : m ≠ 0) :
    Function.Surjective (nsmulAddMonoidHom (α:=restrictedRationalPrimaryImage n hn f) m) := by
  have hp : IsPGroup 2 (Multiplicative (restrictedRationalPrimaryImage n hn f)) := by
    intro x
    obtain ⟨k,hk⟩ := actual_primary_selmer_two_primary n hn x.toAdd.val
    exact ⟨k,Subtype.ext hk⟩
  have hs : Function.Surjective (powMonoidHom (α:=Multiplicative (restrictedRationalPrimaryImage n hn f)) 2) := by
    intro x
    obtain ⟨y,hy⟩ := actual_restricted_primary_two_surjective n hn f x.toAdd
    exact ⟨Multiplicative.ofAdd y,congrArg Multiplicative.ofAdd hy⟩
  intro x
  obtain ⟨y,hy⟩ := actual_primary_all_power_surjective hp hs hm (Multiplicative.ofAdd x)
  exact ⟨y.toAdd,congrArg Multiplicative.toAdd hy⟩

end ActualTwoDescentRestrictedRationalPrimaryDivision318
