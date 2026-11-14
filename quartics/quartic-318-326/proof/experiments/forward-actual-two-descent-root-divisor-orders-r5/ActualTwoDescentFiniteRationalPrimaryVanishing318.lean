module
public import ActualTwoDescentPrimaryRationalAllDivision318
public section
noncomputable section
namespace ActualTwoDescentFiniteRationalPrimaryVanishing318
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

open ActualTwoDescentActualPrimaryRationalImage318 ActualTwoDescentRationalPrimaryTransition318
open ActualTwoDescentPrimaryRationalAllDivision318

/-- If the ACTUAL rational elliptic group is finite, its full rational primary Kummer image vanishes. Actual divisibility and the actual group-order annihilator give the result. -/
theorem actual_finite_rational_primary_zero (n : ℚ) (hn : n ≠ 0) [Finite (Point n)] :
    Subsingleton (rationalPrimaryImage n hn) := by
  have hz (y : rationalPrimaryImage n hn) : Nat.card (Point n) • y=0 := by
    obtain ⟨k,P,hP⟩ := y.property
    apply Subtype.ext
    change Nat.card (Point n) • y.val=0
    rw [←hP,←map_nsmul,card_nsmul_eq_zero',map_zero]
  have hall (x : rationalPrimaryImage n hn) : x=0 := by
    obtain ⟨y,hy⟩ := actual_rational_primary_all_surjective n hn (Nat.card (Point n)) Nat.card_pos.ne' x
    exact hy.symm.trans (hz y)
  exact ⟨fun x y => (hall x).trans (hall y).symm⟩

end ActualTwoDescentFiniteRationalPrimaryVanishing318
