module
public import CTRealNativeNormClass318
public import CTLocalInvariantDescent318
import all CTLocalInvariantDescent318
import all CTRealNativeNormClass318
import all CTContinuousFieldHTwo318
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
public section
noncomputable section

namespace CTRealNativeInvariant318

open CTFieldPrimitiveRestriction318 CTContinuousFieldHTwo318 CTLocalInvariantDescent318
open CTRealNativeNormClass318

local instance : DecidableEq ℝ := Classical.decEq _
local instance : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩

abbrev RealTwoTorsion := (nsmulAddMonoidHom InvValues (2 : ℕ)).ker

def halfValue : InvValues := ((1/2 : ℚ) : AddCircle (1 : ℚ))

theorem halfValue_twice : 2 • halfValue=0 := by
  unfold halfValue
  rw [← AddCircle.coe_nsmul]
  norm_num [two_nsmul,AddCircle.coe_period]

theorem halfValue_ne_zero : halfValue≠0 := by
  have hm : (1/2:ℚ) ∈ Set.Ico 0 1 := by constructor <;> norm_num
  intro h
  have he := (AddCircle.coe_eq_zero_iff_of_mem_Ico hm).1 h
  norm_num at he

private theorem halfValue_add : halfValue+halfValue=0 := by
  simpa only [two_nsmul] using halfValue_twice

private def signValue (z : continuousCycles ℝ) : InvValues :=
  if 0 < signedReal z then 0 else halfValue

private theorem signValue_zero_iff (z : continuousCycles ℝ) :
    signValue z=0 ↔ classOf ℝ z=0 := by
  rw [class_zero_iff_sign]
  unfold signValue
  by_cases h : 0 < signedReal z
  · simp [h]
  · simp [h,halfValue_ne_zero]

private def cycleInvariant : continuousCycles ℝ →+ InvValues where
  toFun := signValue
  map_zero' := by simp [signValue,signedReal_zero]
  map_add' z z' := by
    have hm := signedReal_add z z'
    rcases lt_or_gt_of_ne (signedReal_ne_zero z) with h | h <;>
      rcases lt_or_gt_of_ne (signedReal_ne_zero z') with h' | h'
    · have ht : 0 < signedReal (z+z') := hm.symm ▸ mul_pos_of_neg_of_neg h h'
      simp [signValue,not_lt.mpr h.le,not_lt.mpr h'.le,ht,halfValue_add]
    · have ht : signedReal (z+z') < 0 := hm.symm ▸ mul_neg_of_neg_of_pos h h'
      simp [signValue,not_lt.mpr h.le,h',not_lt.mpr ht.le]
    · have ht : signedReal (z+z') < 0 := hm.symm ▸ mul_neg_of_pos_of_neg h h'
      simp [signValue,h,not_lt.mpr h'.le,not_lt.mpr ht.le]
    · have ht : 0 < signedReal (z+z') := hm.symm ▸ mul_pos h h'
      simp [signValue,h,h',ht]

private theorem cycleInvariant_kills (u : continuousOne ℝ) :
    cycleInvariant (continuousBoundary ℝ u)=0 :=
  (signValue_zero_iff _).2 ((class_zero_iff ℝ _).2 ⟨u,boundary_value ℝ u⟩)

/-- Actual discrete-coefficient H² of the real place has the orientation
0 on positive normalized values and 1/2 on negative values. -/
def actualRealInvariant : ContH2 ℝ →+ InvValues :=
  descendInvariant cycleInvariant cycleInvariant_kills

theorem actualRealInvariant_on_cycle (z : continuousCycles ℝ) :
    actualRealInvariant (classOf ℝ z) = if 0 < signedReal z then 0 else halfValue :=
  descend_invariant_class cycleInvariant cycleInvariant_kills z

private theorem actualRealInvariant_zero (b : ContH2 ℝ) :
    actualRealInvariant b=0 ↔ b=0 := by
  refine QuotientAddGroup.induction_on b ?_
  intro z
  change actualRealInvariant (classOf ℝ z)=0 ↔ classOf ℝ z=0
  rw [actualRealInvariant_on_cycle]
  exact signValue_zero_iff z

private theorem actualRealInvariant_twice (b : ContH2 ℝ) :
    2 • actualRealInvariant b=0 := by
  refine QuotientAddGroup.induction_on b ?_
  intro z
  change 2 • actualRealInvariant (classOf ℝ z)=0
  rw [actualRealInvariant_on_cycle]
  split
  · simp
  · exact halfValue_twice

private def intoTwo : ContH2 ℝ →+ RealTwoTorsion :=
  actualRealInvariant.codRestrict _ (fun b => by
    change 2 • actualRealInvariant b=0
    exact actualRealInvariant_twice b)

private theorem intoTwo_injective : Function.Injective intoTwo := by
  intro b c h
  have he : actualRealInvariant b=actualRealInvariant c :=
    congrArg (fun v : RealTwoTorsion => v.val) h
  apply sub_eq_zero.mp
  apply (actualRealInvariant_zero (b-c)).1
  rw [map_sub,he,sub_self]

private theorem intoTwo_surjective : Function.Surjective intoTwo := by
  intro v
  have hv : 2 • (v : InvValues)=0 := v.property
  obtain ⟨m,hm,he⟩ := (AddCircle.nsmul_eq_zero_iff (by decide : 0 < (2:ℕ))).mp hv
  have hc : m=0 ∨ m=1 := by omega
  rcases hc with rfl | rfl
  · refine ⟨0,Subtype.ext ?_⟩
    change actualRealInvariant 0 = (v : InvValues)
    rw [map_zero,← he]
    norm_num
  · obtain ⟨z,hz⟩ := exists_hamilton_cycle
    refine ⟨classOf ℝ z,Subtype.ext ?_⟩
    change actualRealInvariant (classOf ℝ z) = (v : InvValues)
    rw [actualRealInvariant_on_cycle,hz,if_neg (by norm_num),← he]
    unfold halfValue
    norm_num

def actualRealInvariantEquiv : ContH2 ℝ ≃+ RealTwoTorsion :=
  AddEquiv.ofBijective intoTwo ⟨intoTwo_injective,intoTwo_surjective⟩

theorem hamilton_value : ∃ z : continuousCycles ℝ,
    actualRealInvariant (classOf ℝ z)=halfValue := by
  obtain ⟨z,hz⟩ := exists_hamilton_cycle
  refine ⟨z,?_⟩
  rw [actualRealInvariant_on_cycle,hz,if_neg (by norm_num)]

end CTRealNativeInvariant318
