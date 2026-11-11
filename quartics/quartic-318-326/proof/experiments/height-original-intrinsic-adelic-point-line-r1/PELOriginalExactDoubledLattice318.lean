module
public import PELOriginalDoubledTargetPeriods318
public import PELOriginalPeriodIndex318
public section
noncomputable section
namespace PELOriginalExactDoubledLattice318
open PELOriginalDoubledTargetPeriods318
open RankTwoComplexHalfPeriods318 RankTwoComplexTwoTorsion318
variable (i:Fin 4)
abbrev TargetLattice := PELOriginalCharacterTorus318.periods i
abbrev SourceLattice := PELOriginalInvolutionActualTorus318.periods i
@[expose] def basis : Coordinates≃+TargetLattice i:=
  CompactComplexRankTwoPeriods318.coordinates (TargetLattice i)
@[expose] def modTwo : TargetLattice i→+(Fin 2→ZMod 2):=
  reduction.comp (basis i).symm.toAddMonoidHom
lemma modTwo_surjective : Function.Surjective (modTwo i):=
  reduction_surjective.comp (basis i).symm.surjective

/-- Mod2 is taken in a COMPLETE basis of the actual target lattice. Its
kernel is exactly twice that lattice, not merely the span of two selected
periods or a parity restriction in an ambient coordinate convention. -/
lemma kernel_iff (a:TargetLattice i) : a∈(modTwo i).ker ↔
    ∃b:TargetLattice i,a=(2:ℤ) • b := by
  change reduction ((basis i).symm a)=0 ↔ _
  rw [reduction_kernel]
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨basis i b,?_⟩
    have h:=congrArg (basis i) hb
    simpa only [AddEquiv.apply_symm_apply,map_zsmul] using h
  · rintro ⟨b,rfl⟩
    exact ⟨(basis i).symm b,map_zsmul _ _ _⟩
lemma double_index_four : (modTwo i).ker.index=4 := by
  rw [AddSubgroup.index_eq_card,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective (modTwo i)
      (modTwo_surjective i)).toEquiv,Nat.card_eq_fintype_card]
  norm_num [Fintype.card_fun]
lemma double_kernel_le : (modTwo i).ker≤PELOriginalPeriodIndex318.latticeKernel i := by
  intro a ha
  obtain ⟨b,hb⟩:=(kernel_iff i a).mp ha
  change (a:ℂ)∈SourceLattice i
  rw [hb]
  exact two_zsmul_mem_source i b

/-- The actual source-period index4 and the independently computed
index of2L force equality only AFTER exponent2 gave the inclusion. Index4
alone would also permit cyclic quotients and is not sufficient. -/
theorem kernel_eq : (modTwo i).ker=PELOriginalPeriodIndex318.latticeKernel i := by
  have hr:=AddSubgroup.relIndex_mul_index (modTwo i).ker
    (PELOriginalPeriodIndex318.latticeKernel i) (double_kernel_le i)
  rw [double_index_four,PELOriginalPeriodIndex318.actual_index_four] at hr
  have h1:(modTwo i).ker.relIndex (PELOriginalPeriodIndex318.latticeKernel i)=1:=by omega
  exact le_antisymm (double_kernel_le i) (AddSubgroup.relIndex_eq_one.mp h1)

/-- Exact equality of the actual complex subgroups, point by point:
the full original source periods are precisely twice ALL target periods. -/
theorem source_mem_iff (z:ℂ) : z∈SourceLattice i ↔
    ∃a:TargetLattice i,z=2*(a:ℂ) := by
  constructor
  · intro hz
    have ht:z∈TargetLattice i:=PELOriginalInvolutionActualTorus318.periods_le i hz
    have hk:(⟨z,ht⟩:TargetLattice i)∈(modTwo i).ker:=by
      rw [kernel_eq]
      exact hz
    obtain ⟨a,ha⟩:=(kernel_iff i ⟨z,ht⟩).mp hk
    refine ⟨a,?_⟩
    have hv:=congrArg Subtype.val ha
    change z=(2:ℤ) • (a:ℂ) at hv
    simpa only [two_zsmul,two_mul] using hv
  · rintro ⟨a,rfl⟩
    have h:=double_mem_source i a.val a.property
    simpa only [two_mul] using h
end PELOriginalExactDoubledLattice318
