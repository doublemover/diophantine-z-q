module
public import ActualTwoDescentActualPrimarySelmerDivisible318
public section
noncomputable section
namespace ActualTwoDescentPrimaryRationalAllDivision318
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

open ActualTwoDescentActualPrimaryRationalImage318 ActualTwoDescentRationalPrimaryDivision318
open ActualTwoDescentFullPrimarySelmerTorsion318 ActualTwoDescentPrimaryAllRoots318

lemma actual_rational_primary_all_surjective (n : ℚ) (hn : n ≠ 0) (m : ℕ) (hm : m ≠ 0) :
    Function.Surjective (nsmulAddMonoidHom (α:=rationalPrimaryImage n hn) m) := by
  have hp : IsPGroup 2 (Multiplicative (rationalPrimaryImage n hn)) := by
    intro x
    obtain ⟨k,hk⟩ := actual_primary_selmer_two_primary n hn x.toAdd.val
    exact ⟨k,Subtype.ext hk⟩
  have hs : Function.Surjective (powMonoidHom (α:=Multiplicative (rationalPrimaryImage n hn)) 2) := by
    intro x
    obtain ⟨y,hy⟩ := actual_rational_primary_two_surjective n hn x.toAdd
    exact ⟨Multiplicative.ofAdd y,congrArg Multiplicative.ofAdd hy⟩
  intro x
  obtain ⟨y,hy⟩ := actual_primary_all_power_surjective hp hs hm (Multiplicative.ofAdd x)
  exact ⟨y.toAdd,congrArg Multiplicative.toAdd hy⟩

end ActualTwoDescentPrimaryRationalAllDivision318
