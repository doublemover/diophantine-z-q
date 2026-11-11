module
public import FourRootZeroSchemeSupport318
public import PELOriginalContactSchemePoints318
public import PELOriginalZeroQuotientLengths318
public section
noncomputable section
namespace PELOriginalZeroSchemeSupport318
open scoped OnePoint
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalContactRootFunctions318 PELOriginalCompletedContactPoints318
open PELOriginalBranchLabels318 FourRootCompletedSchemePoints318
/-- Support is defined by the SAME closed immersion on the SAME actual
Scheme-valued original point, before identifying it with ramification. -/
def InZero (p : UnlevelledBase) : Prop :=
  (PELOriginalContactSchemePoints318.comparison p).val default ∈
    Set.range (FourRootGluedDerivativeIdeal318.into branches)
lemma regular_not_in_zero (p : UnlevelledBase) (hp : p ∈ RegularSource) : ¬InZero p := by
  unfold InZero
  rw [PELOriginalContactSchemePoints318.comparison_value,completedMap_regular p hp]
  change ¬((finitePoint branches ⟨(base p,roots p),roots_square p hp⟩).val default ∈ _)
  rw [FourRootZeroSchemeSupport318.finite_support]
  intro h
  obtain ⟨i,hi⟩ := h
  exact ((FourRootPuncturedRegularity318.denominator_ne_iff branches (base p)).mp
    (denominator_ne p hp)) i hi
lemma ramified_in_zero (p : UnlevelledBase) (hp : p ∈ nontrivialStabilizerLocus) : InZero p := by
  unfold InZero
  rw [PELOriginalContactSchemePoints318.comparison_value]
  by_cases hi : normalizedMap p = ∞
  · rw [completedMap_infinity p hp hi]
    exact FourRootZeroSchemeSupport318.infinity_center branches _
  · have hr := not_regular_of_ramified p hp
    rw [completedMap_finiteBranch p hp (branchIndex p hr hi) (branchIndex_value p hr hi)]
    apply (FourRootZeroSchemeSupport318.finite_support branches _).mpr
    exact ⟨branchIndex p hr hi,rfl⟩
/-- The original derivative-zero closed scheme has exactly the entire
original stabilizer support on complex points, including all infinity signs. -/
theorem support_iff (p : UnlevelledBase) : InZero p ↔ p ∈ nontrivialStabilizerLocus := by
  constructor
  · intro h
    apply ramified_of_not_regular p
    intro hp
    exact regular_not_in_zero p hp h
  · exact ramified_in_zero p
end PELOriginalZeroSchemeSupport318
