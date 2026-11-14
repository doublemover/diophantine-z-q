module
public import ActualTwoDescentFullPrimarySelmerTorsion318
public section
noncomputable section
namespace ActualTwoDescentActualShaPrimaryDivision318
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

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaReducedDuality318
open ActualTwoDescentActualShaZeroPrueferDuality318 ActualTwoDescentActualShaReducedPrimary318
open ActualTwoDescentInfinitePrimaryDivisible318 ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

lemma actual_sha_primary_two_surjective_of_duality (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (hdual : ActualReducedDuality n hn) :
    Function.Surjective (nsmulAddMonoidHom (α:=Additive (actualShaPrimary n hn)) 2) := by
  rcases actual_sha_zero_or_pruefer_of_duality n hn hf hb hS hdual with hz|⟨hi,_⟩
  · letI := hz
    intro x
    exact ⟨0,Subsingleton.elim _ _⟩
  · letI := hi
    obtain ⟨ht,hc⟩ := actual_sha_primary_level_bounds n hn hf hb hS
    intro x
    obtain ⟨y,hy⟩ := actual_infinite_primary_square_surjective _ (actual_sha_primary_is_two_group n hn) ht hc x.toMul
    exact ⟨Additive.ofMul y,congrArg Additive.ofMul hy⟩

end ActualTwoDescentActualShaPrimaryDivision318
