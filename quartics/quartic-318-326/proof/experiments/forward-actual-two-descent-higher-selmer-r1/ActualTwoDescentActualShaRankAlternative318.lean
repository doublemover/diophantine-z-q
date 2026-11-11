module
public import ActualTwoDescentActualShaObstructionEquivalence318
public section
noncomputable section
namespace ActualTwoDescentActualShaRankAlternative318
set_option maxHeartbeats 16000000

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldHalvingCocycle318
open ActualTwoDescentFieldHalvingChoiceIndependence318 ActualTwoDescentFieldGaloisLocallyConstant318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldActualCohomologicalImage318
open groupCohomology

open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentActualShaDefinition318
open ActualTwoDescentActualShaObstructionEquivalence318 ActualTwoDescentObstructionCardinality318
open ActualTwoDescentAllPlacesIntersection318

/-- The exact unresolved alternative is now about GENUINE elliptic Sha[2]. No finiteness or parity theorem for full Sha is assumed. -/
theorem actual_sha_rank_alternative (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) :
    (Nat.card (DoubleQuotient n)=4 ∧ Nat.card (actualShaTwo n hn)=2 ∧ Finite (Point n)) ∨
    (Nat.card (DoubleQuotient n)=8 ∧ Nat.card (actualShaTwo n hn)=1 ∧ Infinite (Point n)) := by
  simpa only [actual_sha_obstruction_cardinality] using actual_obstruction_alternative n hn hf hb hS

lemma actual_sha_one_iff_infinite (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) :
    Nat.card (actualShaTwo n hn)=1 ↔ Infinite (Point n) := by
  rw [actual_sha_obstruction_cardinality]
  exact actual_obstruction_one_iff_infinite n hn hf hb hS

end ActualTwoDescentActualShaRankAlternative318
