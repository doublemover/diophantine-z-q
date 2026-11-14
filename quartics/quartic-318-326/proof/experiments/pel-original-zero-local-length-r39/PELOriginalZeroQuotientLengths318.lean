module
public import FourRootFiniteZeroLocalLength318
public import FourRootInfinityZeroLocalLength318
public import PELOriginalActualDifferentDivisor318
public section
noncomputable section
namespace PELOriginalZeroQuotientLengths318
open scoped OnePoint BigOperators Classical
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalContactRootFunctions318 PELOriginalCompletedContactPoints318
open PELOriginalBranchLabels318 FourRootNormalizedPointCharts318
/-- Actual local quotient lengths along the ORIGINAL completed contact
point map. These are module lengths, independently of the earlier
uniformizer-valuation definition of the different divisor. -/
@[expose] def localLength(p:UnlevelledBase):ℕ∞:=
  match completedMap p with
  | .inl q=>FourRootFiniteZeroLocalLength318.localLength branches q
  | .inr s=>FourRootInfinityZeroLocalLength318.localLength branches (center branches s)
lemma regular_length(p:UnlevelledBase)(hp:p∈RegularSource):localLength p=0:=by
  rw [localLength,completedMap_regular p hp]
  apply FourRootFiniteZeroLocalLength318.regular_length branches branches_injective
  exact (FourRootPuncturedRegularity318.denominator_ne_iff branches (base p)).mp
    (denominator_ne p hp)
lemma branch_length(p:UnlevelledBase)(hp:p∈nontrivialStabilizerLocus):localLength p=1:=by
  by_cases hi:normalizedMap p=∞
  · rw [localLength,completedMap_infinity p hp hi]
    exact FourRootInfinityZeroLocalLength318.center_length branches branches_injective _ rfl
  · have hr:=not_regular_of_ramified p hp
    rw [localLength,completedMap_finiteBranch p hp (branchIndex p hr hi) (branchIndex_value p hr hi)]
    exact FourRootFiniteZeroLocalLength318.branch_length branches branches_injective _ _ rfl
/-- Equality is PROVED between the true local quotient length and the
independently constructed trace-different coefficient. -/
theorem length_equals_different(p:UnlevelledBase):
    localLength p=(PELOriginalActualDifferentDivisor318.coefficient p:ℕ∞):=by
  rw [PELOriginalActualDifferentDivisor318.exact_coefficient]
  by_cases hp:p∈nontrivialStabilizerLocus
  · rw [if_pos hp,Nat.cast_one]
    exact branch_length p hp
  · rw [if_neg hp,Nat.cast_zero]
    apply regular_length
    by_contra hr
    exact hp (ramified_of_not_regular p hr)
/-- All forty ORIGINAL ramification points contribute their actual
local quotient length one. This is not yet a global coherent sheaf
length theorem or a whole-scheme reducedness theorem. -/
theorem total_length_forty:
    (∑p:PELOriginalFiniteRamification318.Ramification,localLength p.val)=40:=by
  have h:∀p:PELOriginalFiniteRamification318.Ramification,localLength p.val=1:=
    fun p=>branch_length p.val p.property
  have hc:Fintype.card PELOriginalFiniteRamification318.Ramification=40:=
    PELOriginalDirectBranchEnumeration318.actual_branch_and_ramification_counts.2
  simp_rw [h]
  simp [hc]
end PELOriginalZeroQuotientLengths318
