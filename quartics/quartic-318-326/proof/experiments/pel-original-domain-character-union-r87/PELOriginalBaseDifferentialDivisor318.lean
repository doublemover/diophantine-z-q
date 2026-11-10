module
public import FourRootActualBaseDifferentialOrders318
public import PELOriginalActualDifferentDivisor318
public import PELOriginalCompletedContactBiholomorph318
public section
noncomputable section
namespace PELOriginalBaseDifferentialDivisor318
open scoped OnePoint BigOperators Classical
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalContactRootFunctions318 PELOriginalCompletedContactPoints318
open PELOriginalBranchLabels318 FourRootNormalizedPointCharts318
/-- Actual signed order of the ORIGINAL meromorphic base differential
at the SAME original full source point. Both cases use genuine local
DVR valuations of actual intrinsic-frame coefficients, not e(P)-1. -/
@[expose] def coefficient(p:UnlevelledBase):ℤ:=
  match completedMap p with
  | .inl q=>FourRootActualFiniteDifferentialOrders318.order branches branches_injective q
  | .inr s=>FourRootActualInfinityDifferentialOrders318.order branches branches_injective
      (center branches s) rfl
lemma regular_coefficient(p:UnlevelledBase)(hp:p∈RegularSource):coefficient p=0:=by
  rw [coefficient,completedMap_regular p hp]
  apply FourRootActualFiniteDifferentialOrders318.regular_order branches branches_injective
  exact (FourRootPuncturedRegularity318.denominator_ne_iff branches (base p)).mp
    (denominator_ne p hp)
lemma finite_branch_coefficient(p:UnlevelledBase)(hp:p∈nontrivialStabilizerLocus)
    (hi:normalizedMap p≠∞):coefficient p=1:=by
  have hr:=not_regular_of_ramified p hp
  rw [coefficient,completedMap_finiteBranch p hp (branchIndex p hr hi) (branchIndex_value p hr hi)]
  exact FourRootActualFiniteDifferentialOrders318.branch_order branches branches_injective _ _ rfl
lemma infinity_ramified(p:UnlevelledBase)(hi:normalizedMap p=∞):p∈nontrivialStabilizerLocus:=by
  apply ramified_of_not_regular
  intro hr
  exact OnePoint.coe_ne_infty (base p) ((normalized_finite p hr).symm.trans hi)
lemma infinity_coefficient(p:UnlevelledBase)(hi:normalizedMap p=∞):coefficient p=-3:=by
  rw [coefficient,completedMap_infinity p (infinity_ramified p hi) hi]
  exact FourRootActualInfinityDifferentialOrders318.order_minus_three branches branches_injective _ rfl
/-- The RH-shaped formula is DERIVED from actual different ideals and
actual differential coefficients. At infinity e=2 but ord(dt)=-3,
so the pulled-back order -2 of dt on P¹ contributes -4 there. -/
theorem actual_different_comparison(p:UnlevelledBase):
    coefficient p=(PELOriginalActualDifferentDivisor318.coefficient p:ℤ)-
      (if normalizedMap p=∞ then 4 else 0):=by
  by_cases hi:normalizedMap p=∞
  · rw [infinity_coefficient p hi,
      PELOriginalActualDifferentDivisor318.branch_coefficient p (infinity_ramified p hi),if_pos hi]
    norm_num
  · rw [if_neg hi,sub_zero]
    by_cases hp:p∈nontrivialStabilizerLocus
    · rw [finite_branch_coefficient p hp hi,PELOriginalActualDifferentDivisor318.branch_coefficient p hp]
      rfl
    · have hr:p∈RegularSource:=by
        by_contra hn
        exact hp (ramified_of_not_regular p hn)
      rw [regular_coefficient p hr,PELOriginalActualDifferentDivisor318.regular_coefficient p hr]
      rfl

/-- A finite-support coefficient divisor of the actual meromorphic
differential on original complex points. This is not a new algebraic
Cartier-divisor object or a supplied canonical-sheaf identification. -/
@[expose] def divisor:UnlevelledBase→₀ℤ:=
  Finsupp.onFinset PELOriginalActualDifferentDivisor318.support coefficient (by
    intro p hp
    apply (PELOriginalActualDifferentDivisor318.support_iff p).mpr
    by_contra hn
    have hr:p∈RegularSource:=by
      by_contra hnr
      exact hn (ramified_of_not_regular p hnr)
    exact hp (regular_coefficient p hr))
lemma divisor_apply(p:UnlevelledBase):divisor p=coefficient p:=rfl
lemma support_exact(p:UnlevelledBase):divisor p≠0↔p∈nontrivialStabilizerLocus:=by
  constructor
  · intro h
    by_contra hn
    have hr:p∈RegularSource:=by
      by_contra hnr
      exact hn (ramified_of_not_regular p hnr)
    exact h (regular_coefficient p hr)
  · intro hp
    rw [divisor_apply]
    by_cases hi:normalizedMap p=∞
    · rw [infinity_coefficient p hi];norm_num
    · rw [finite_branch_coefficient p hp hi];norm_num

abbrev Ramification:=PELOriginalFiniteRamification318.Ramification
abbrev InfinityRamification:={p:Ramification//normalizedMap p.val=∞}
@[expose] def infinityFiberEquiv:InfinityRamification≃{p:UnlevelledBase//normalizedMap p=∞} where
  toFun p:=⟨p.val.val,p.property⟩
  invFun p:=⟨⟨p.val,infinity_ramified p.val p.property⟩,p.property⟩
  left_inv _:=rfl
  right_inv _:=rfl
lemma infinity_card:Fintype.card InfinityRamification=8:=by
  rw [←Nat.card_eq_fintype_card,Nat.card_congr infinityFiberEquiv]
  exact PELOriginalCompletedContactBiholomorph318.infinity_card
/-- Degree EIGHT of the actual dt coefficient divisor on the original
genus-five, degree-sixteen curve: thirty-two simple zeros and eight
order-three poles. No elliptic-factor or j-sphere divisor is substituted. -/
theorem degree_eight:(∑p:Ramification,divisor p.val)=8:=by
  have hpoint:∀p:Ramification,divisor p.val=1-(if normalizedMap p.val=∞ then 4 else 0):=by
    intro p
    rw [divisor_apply,actual_different_comparison,
      PELOriginalActualDifferentDivisor318.branch_coefficient p.val p.property]
    rfl
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  have htotal:Fintype.card Ramification=40:=
    PELOriginalDirectBranchEnumeration318.actual_branch_and_ramification_counts.2
  have hi:(∑p:Ramification,if normalizedMap p.val=∞ then (4:ℤ) else 0)=32:=by
    rw [←Finset.sum_filter]
    rw [Finset.sum_subtype (Finset.univ.filter (fun p:Ramification=>normalizedMap p.val=∞))
      (by intro p;simp) (fun _=> (4:ℤ))]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,infinity_card]
    norm_num
  rw [hi]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,htotal]
  norm_num
end PELOriginalBaseDifferentialDivisor318
