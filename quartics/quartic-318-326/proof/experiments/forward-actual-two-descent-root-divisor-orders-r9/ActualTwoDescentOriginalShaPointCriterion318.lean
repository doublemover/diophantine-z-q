module
public import ActualTwoDescentActualShaRankAlternative318
public section
noncomputable section
namespace ActualTwoDescentOriginalShaPointCriterion318
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
open ActualTwoDescentBetaPointRankEquivalence318 ActualTwoDescentPointExtraction318
open ActualTwoDescentRationalEightClasses318 ActualTwoDescentActualQuotientBound318
open ActualTwoDescentSameRationalBounds318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentAllPlacesIntersection318
open scoped BigOperators

/-- Exact original beta-point criterion in terms of the ACTUAL elliptic Sha[2]. The vanishing is NOT assumed as an untracked producer. -/
theorem actual_original_sha_point_iff {U : Type*} [Fintype U] [DecidableEq U]
    (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (hn : (∏ i, p i) ≠ 0) (hb : monomial p beta ≠ 0)
    (hlocal : Nat.card (allPlacesImage ((∏ i, p i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn))=8) :
    Nonempty (KummerPoint (monomial p beta : ℚ) ((∏ i, p i : ℕ) : ℚ)) ↔
      Nat.card (actualShaTwo ((∏ i, p i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn))=1 := by
  have HR : RationalEightBound (∏ i, p i) (monomial p beta) := by
    intro P
    exact actual_rational_eight_classes p hd hp2 hp3 a beta N C P
  obtain ⟨hf,hbound⟩ := actual_quotient_finite_bound _ _ hn hb HR
  exact (actual_beta_point_iff_infinite p hd hp2 hp3 a beta N C hn hb hlocal).trans
    (actual_sha_one_iff_infinite _ _ hf hbound hlocal).symm

end ActualTwoDescentOriginalShaPointCriterion318
