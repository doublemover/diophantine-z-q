module
public import ActualTwoDescentOriginalShaPointCriterion318
public section
noncomputable section
namespace ActualTwoDescentFourActualShaConsumer318
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

open ActualTwoDescentActualShaDefinition318 ActualTwoDescentActualShaRankAlternative318
open ActualTwoDescentMordellWeilControl318 ActualTwoDescentFourInfinitePointConsumer318
open ActualTwoDescentOriginalAllPlacesCardinality318 TwoTwistPointRealization318

/-- SAME-index four-label consumer: the remaining input is stated as actual Sha[2] vanishing on BOTH original twists, never replaced by local solubility. -/
theorem actual_four_realizations_of_sha_one
    (b c d : Fin 4 → ℚ) (beta theta n : Fin 4 → ℕ)
    (hb : ∀ i, beta i ≠ 0) (hc : ∀ i, c i ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hB : ∀ i, 17*b i=(beta i : ℚ)*(c i)^2)
    (hV : ∀ i, (17*b i)^2*(1-b i/17)=(theta i : ℚ)*(d i)^2)
    (C : ∀ i, MordellWeilControl (n i) (beta i))
    (Ctwist : ∀ i, MordellWeilControl (n i*theta i) (beta i))
    (hS : ∀ i, AllPlacesEight (n i)) (hStwist : ∀ i, AllPlacesEight (n i*theta i))
    (hSha : ∀ i (hn : n i ≠ 0), Nat.card (actualShaTwo (n i : ℚ) (Nat.cast_ne_zero.mpr hn))=1)
    (hShaTwist : ∀ i (hn : n i*theta i ≠ 0), Nat.card (actualShaTwo ((n i*theta i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn))=1) :
    Nonempty (∀ i, Realization (b i)) := by
  apply actual_four_realizations_of_infinite b c d beta theta n hb hc hd hB hV C Ctwist
  · intro i
    obtain ⟨hn,hs⟩ := hS i
    exact (actual_sha_one_iff_infinite _ _ (C i).1.2.1 (C i).1.2.2.1 hs).mp (hSha i hn)
  · intro i
    obtain ⟨hn,hs⟩ := hStwist i
    exact (actual_sha_one_iff_infinite _ _ (Ctwist i).1.2.1 (Ctwist i).1.2.2.1 hs).mp (hShaTwist i hn)

end ActualTwoDescentFourActualShaConsumer318
