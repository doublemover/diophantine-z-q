module
public import PELOriginalRegularCharacterProduct318
public import FourCharacterRootRecombination318
public section
noncomputable section
namespace PELOriginalCommonContactBase318
open Set
open scoped OnePoint
open PELOriginalMaximalQuotient318 PELOriginalMarkedSphere318
open PELOriginalManuscriptNormalization318 PELStabilizerLocusInvariant318

/-- Finite branch order is the OMITTED CHARACTER order105,70,42,30.
This differs from both printed row order and the original five-label order.
The same original label210 remains infinity. -/
@[expose] def branches : Fin 4→ℂ:=![0,1,lambda,mu]
@[expose] def labels : Fin 4→Fin 5:=![3,2,1,0]
lemma labels_injective : Function.Injective labels:=by decide
lemma branch_values (i:Fin 4) : coordinate (branchPoint (labels i))=(branches i:OnePoint ℂ):=by
  fin_cases i
  · exact value105
  · exact value70
  · exact value42
  · exact value30
lemma branches_injective : Function.Injective branches:=by
  intro i j h
  apply labels_injective
  apply branchPoint_injective
  apply coordinate.injective
  rw [branch_values,branch_values,h]

/-- Exact original maximal-base point of a finite manuscript coordinate. -/
@[expose] def basePoint (t:ℂ):MaximalBase:=coordinate.symm (t:OnePoint ℂ)
lemma basePoint_value (t:ℂ):coordinate (basePoint t)=(t:OnePoint ℂ):=
  coordinate.apply_symm_apply _
lemma base_branch_iff (t:ℂ):basePoint t∈branchImage ↔
    t=0 ∨ t=1 ∨ t=lambda ∨ t=mu := by
  have hm:basePoint t∈branchImage ↔
      coordinate (basePoint t)∈coordinate '' branchImage:=by
    constructor
    · intro h;exact ⟨basePoint t,h,rfl⟩
    · rintro ⟨q,hq,hqt⟩
      exact coordinate.injective hqt ▸ hq
  rw [hm,branch_image,basePoint_value]
  simp only [mem_insert_iff,mem_singleton_iff,OnePoint.coe_ne_infty,
    OnePoint.coe_inj,false_or]
lemma regular_iff (t:ℂ):basePoint t∉branchImage ↔
    FourCharacterRootRecombination318.denominator branches t≠0 := by
  rw [base_branch_iff]
  simp only [FourCharacterRootRecombination318.denominator,
    FourCharacterRootRecombination318.product,FourCharacterRootRecombination318.linear,
    branches,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    sub_zero,mul_ne_zero_iff,sub_ne_zero]
  tauto

/-- The actual genus-five source over any regular COMMON manuscript t
has all four compatible intermediate points at once. The exact branch
polynomial controlling later root recombination is derived from the full
original branch image, not merely from a chosen finite subset. -/
@[expose] def genericFiber (t:ℂ)
    (h:FourCharacterRootRecombination318.denominator branches t≠0) :
    PELOriginalRegularCharacterProduct318.SourceFiber (basePoint t) ≃
      (∀i,PELOriginalRegularCharacterProduct318.CharacterFiber (basePoint t) i):=
  PELOriginalRegularCharacterProduct318.regularEquiv (basePoint t) ((regular_iff t).mpr h)
end PELOriginalCommonContactBase318
