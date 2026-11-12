module
public import ActualTwoDescentFiniteRankSelmerPruefer318
public section
noncomputable section
namespace ActualTwoDescentPrimarySelmerAllDivision318
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

open ActualTwoDescentActualPrimarySelmerDivisible318 ActualTwoDescentFullPrimarySelmerTorsion318
open ActualTwoDescentPrimaryAllRoots318 ActualTwoDescentActualShaReducedDuality318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- The actual full primary Selmer group is genuinely divisible by every nonzero integer, conditional only on the explicitly missing global reduced pairing and existing actual arithmetic bounds. -/
theorem actual_primary_selmer_all_surjective (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (hdual : ActualReducedDuality n hn) (m : ℕ) (hm : m ≠ 0) :
    Function.Surjective (nsmulAddMonoidHom (α:=actualPrimarySelmer n hn) m) := by
  have hp : IsPGroup 2 (Multiplicative (actualPrimarySelmer n hn)) := by
    intro x
    exact actual_primary_selmer_two_primary n hn x.toAdd
  have hs : Function.Surjective (powMonoidHom (α:=Multiplicative (actualPrimarySelmer n hn)) 2) := by
    intro x
    obtain ⟨y,hy⟩ := actual_primary_selmer_two_surjective n hn hf hb hS hdual x.toAdd
    exact ⟨Multiplicative.ofAdd y,congrArg Multiplicative.ofAdd hy⟩
  intro x
  obtain ⟨y,hy⟩ := actual_primary_all_power_surjective hp hs hm (Multiplicative.ofAdd x)
  exact ⟨y.toAdd,congrArg Multiplicative.toAdd hy⟩

end ActualTwoDescentPrimarySelmerAllDivision318
