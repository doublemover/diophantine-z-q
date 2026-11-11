module
public import FourRootOffBranchRamification318
public import PELOriginalAlgebraicInfinityRamification318
public import PELOriginalDirectBranchEnumeration318
public section
noncomputable section
namespace PELOriginalAlgebraicRamificationSupport318
open scoped OnePoint BigOperators Classical
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalContactRootFunctions318 PELOriginalCompletedContactPoints318
open PELOriginalBranchLabels318 FourRootNormalizedPointCharts318

@[expose] def finiteIndex (q:FinitePoints branches):ℕ:=
  letI:Algebra (Polynomial ℂ) (FourRootAffineCoordinateRing318.Ring branches):=
    (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate branches none)).toAlgebra
  (FourRootActualResidueInertia318.finitePrime branches q).ramificationIdx (Polynomial ℂ)
@[expose] def infinityIndex (s:InfinitySigns):ℕ:=
  letI:Algebra (Polynomial ℂ) (FourRootInfinityCoordinateRing318.Ring branches):=
    (Polynomial.aeval (FourRootInfinityCoordinateRing318.coordinate branches none^2)).toAlgebra
  (FourRootActualResidueInertia318.infinityPrime branches (center branches s)).ramificationIdx (Polynomial ℂ)
/-- Actual algebraic chart-ideal ramification index of the SAME original
Scheme-valued point. Infinity uses the true reciprocal projective base. -/
@[expose] def index (p:UnlevelledBase):ℕ:=
  match completedMap p with
  | .inl q=>finiteIndex q
  | .inr s=>infinityIndex s

lemma regular_index (p:UnlevelledBase) (hp:p∈RegularSource):index p=1:=by
  rw [index,completedMap_regular p hp]
  apply FourRootOffBranchRamification318.ramificationIdx_one branches branches_injective
  exact (FourRootPuncturedRegularity318.denominator_ne_iff branches (base p)).mp
    (denominator_ne p hp)
lemma branch_index (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus):index p=2:=by
  by_cases hi:normalizedMap p=∞
  · rw [index,completedMap_infinity p hp hi]
    exact FourRootActualInfinityRamification318.ramificationIdx_two branches branches_injective
      (center branches (infinityCenter p hp hi)) rfl
  · have hr:=not_regular_of_ramified p hp
    rw [index,completedMap_finiteBranch p hp (branchIndex p hr hi) (branchIndex_value p hr hi)]
    exact FourRootActualFiniteRamification318.ramificationIdx_two branches branches_injective
      (branchIndex p hr hi) (finiteCenter p hp _ _) rfl

/-- Full algebraic branch support equals the original genuine stabilizer
locus. No extra finite branch points or collapsed infinity points remain. -/
theorem exact_index (p:UnlevelledBase):
    index p=if p∈nontrivialStabilizerLocus then 2 else 1:=by
  by_cases hp:p∈nontrivialStabilizerLocus
  · rw [if_pos hp];exact branch_index p hp
  · rw [if_neg hp]
    apply regular_index
    by_contra hr
    exact hp (ramified_of_not_regular p hr)

theorem algebraic_ramified_iff (p:UnlevelledBase):
    index p≠1 ↔ p∈nontrivialStabilizerLocus:=by
  rw [exact_index]
  split_ifs <;> simp_all

/-- Sum of genuine algebraic e(P)-1 over the ENTIRE original ramification
locus. This is degree40 on the degree16 genus-five source, not degree6 on
the separate j parameter sphere. No Kahler/different identity is assumed. -/
theorem total_index_excess:
    (∑p:PELOriginalFiniteRamification318.Ramification,index p.val-1)=40:=by
  have h:∀p:PELOriginalFiniteRamification318.Ramification,index p.val-1=1:=by
    intro p
    rw [branch_index p.val p.property]
  simp_rw [h]
  simpa using PELOriginalDirectBranchEnumeration318.actual_branch_and_ramification_counts.2
end PELOriginalAlgebraicRamificationSupport318
