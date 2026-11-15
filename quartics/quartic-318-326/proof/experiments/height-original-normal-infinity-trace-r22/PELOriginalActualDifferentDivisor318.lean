module
public import FourRootLocalDifferentMultiplicity318
public import PELOriginalAlgebraicRamificationSupport318
public import Mathlib.Data.Finsupp.Defs
public section
noncomputable section
namespace PELOriginalActualDifferentDivisor318
open scoped OnePoint BigOperators Classical
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalContactRootFunctions318 PELOriginalCompletedContactPoints318
open PELOriginalBranchLabels318 FourRootNormalizedPointCharts318
/-- Actual normalized valuations of genuine trace-dual different
ideals at the SAME original Scheme-valued point. Infinity retains its
actual sign triple and reciprocal v=u² base. -/
@[expose] def coefficient(p:UnlevelledBase):ℕ:=
  match completedMap p with
  | .inl q=>FourRootLocalDifferentMultiplicity318.finiteCoefficient branches branches_injective q
  | .inr s=>FourRootInfinityDifferentMultiplicity318.coefficient branches branches_injective
      (center branches s) rfl
lemma regular_coefficient(p:UnlevelledBase)(hp:p∈RegularSource):coefficient p=0:=by
  rw [coefficient,completedMap_regular p hp]
  apply FourRootLocalDifferentMultiplicity318.finite_regular branches branches_injective
  exact (FourRootPuncturedRegularity318.denominator_ne_iff branches (base p)).mp
    (denominator_ne p hp)
lemma branch_coefficient(p:UnlevelledBase)(hp:p∈nontrivialStabilizerLocus):coefficient p=1:=by
  by_cases hi:normalizedMap p=∞
  · rw [coefficient,completedMap_infinity p hp hi]
    exact FourRootInfinityDifferentMultiplicity318.coefficient_one branches branches_injective _ rfl
  · have hr:=not_regular_of_ramified p hp
    rw [coefficient,completedMap_finiteBranch p hp (branchIndex p hr hi) (branchIndex_value p hr hi)]
    exact FourRootLocalDifferentMultiplicity318.finite_branch branches branches_injective _ _ rfl
/-- This coefficient formula is a CONSEQUENCE of the actual different
stalk computations, not its definition by ramification index or support. -/
theorem exact_coefficient(p:UnlevelledBase):
    coefficient p=if p∈nontrivialStabilizerLocus then 1 else 0:=by
  by_cases hp:p∈nontrivialStabilizerLocus
  · rw [if_pos hp];exact branch_coefficient p hp
  · rw [if_neg hp]
    apply regular_coefficient
    by_contra hr
    exact hp (ramified_of_not_regular p hr)
theorem different_equals_index_excess(p:UnlevelledBase):
    coefficient p=PELOriginalAlgebraicRamificationSupport318.index p-1:=by
  rw [exact_coefficient,PELOriginalAlgebraicRamificationSupport318.exact_index]
  split_ifs <;> rfl

@[expose] def support:Finset UnlevelledBase:=
  Finset.univ.image (fun p:PELOriginalFiniteRamification318.Ramification=>p.val)
lemma support_iff(p:UnlevelledBase):p∈support↔p∈nontrivialStabilizerLocus:=by
  constructor
  · intro h
    obtain ⟨q,_,hq⟩:=Finset.mem_image.mp h
    exact hq ▸ q.property
  · intro hp
    exact Finset.mem_image.mpr ⟨⟨p,hp⟩,Finset.mem_univ _,rfl⟩
/-- Finitely supported effective different coefficient function on the
original genus-five source. All40 original ramification points occur,
each once; no j-parameter or elliptic quotient divisor is substituted. -/
@[expose] def divisor:UnlevelledBase→₀ℕ:=
  Finsupp.onFinset support coefficient (by
    intro p hp
    apply (support_iff p).mpr
    by_contra hn
    exact hp (by rw [exact_coefficient,if_neg hn]))
lemma divisor_apply(p:UnlevelledBase):divisor p=coefficient p:=rfl

theorem degree_forty:
    (∑p:PELOriginalFiniteRamification318.Ramification,divisor p.val)=40:=by
  have h:∀p:PELOriginalFiniteRamification318.Ramification,divisor p.val=1:=by
    intro p
    rw [divisor_apply,branch_coefficient p.val p.property]
  simp_rw [h]
  simpa using PELOriginalDirectBranchEnumeration318.actual_branch_and_ramification_counts.2
end PELOriginalActualDifferentDivisor318
