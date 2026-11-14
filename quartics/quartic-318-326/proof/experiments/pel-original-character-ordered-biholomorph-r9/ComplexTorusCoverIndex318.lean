module
public import ComplexTorusCoverPeriods318
public section
noncomputable section
namespace ComplexTorusCoverIndex318
open Set Topology
open ComplexLineLatticeAtlas318 ComplexTorusCoverLift318 ComplexTorusCoverPeriods318
variable (L:AddSubgroup ℂ) [DiscreteTopology L]
variable {E:Type*} [TopologicalSpace E] [PathConnectedSpace E]
variable (p:E→Quotient L) (cov:IsCoveringMap p) (e₀:E) (he:p e₀=projection L 0)

/-- The actual source periods regarded as a subgroup of the SAME target
lattice. Its index is not the index of a separately rescaled lattice. -/
@[expose] def latticeKernel : AddSubgroup L :=
  (periods L p cov e₀ he).comap L.subtype
abbrev Fiber := {e:E // p e=projection L 0}

@[expose] def fiberMap (a:L) : Fiber L p :=
  ⟨lift L p cov e₀ he a,by
    rw [lift_projection]
    change (QuotientAddGroup.mk' L) (a:ℂ)=0
    exact QuotientAddGroup.eq_zero_iff.mpr a.property⟩
lemma fiberMap_surjective : Function.Surjective (fiberMap L p cov e₀ he) := by
  intro e
  obtain ⟨z,hz⟩:=lift_surjective L p cov e₀ he e.val
  have hzL:z∈L:=by
    apply QuotientAddGroup.eq_zero_iff.mp
    change projection L z=projection L 0
    rw [←lift_projection L p cov e₀ he z,hz]
    exact e.property
  exact ⟨⟨z,hzL⟩,Subtype.ext hz⟩

lemma quotient_fiber (a b:L) :
    (QuotientAddGroup.mk' (latticeKernel L p cov e₀ he)) a=
      (QuotientAddGroup.mk' (latticeKernel L p cov e₀ he)) b ↔
    fiberMap L p cov e₀ he a=fiberMap L p cov e₀ he b := by
  rw [←sub_eq_zero,←map_sub,QuotientAddGroup.eq_zero_iff]
  change (a:ℂ)-(b:ℂ)∈periods L p cov e₀ he ↔ _
  rw [←fiber_iff L p cov e₀ he]
  exact Subtype.ext_iff.symm

/-- Descending the ACTUAL lift on target lattice points gives the whole
original zero fiber, including its actual points and no invented group
structure on that fiber. -/
@[expose] def fiberEquiv : (L ⧸ latticeKernel L p cov e₀ he)≃Fiber L p where
  toFun q:=fiberMap L p cov e₀ he
    (QuotientAddGroup.mk'_surjective (latticeKernel L p cov e₀ he) q).choose
  invFun e:=(QuotientAddGroup.mk' (latticeKernel L p cov e₀ he))
    (fiberMap_surjective L p cov e₀ he e).choose
  left_inv q:=by
    let a:=(QuotientAddGroup.mk'_surjective (latticeKernel L p cov e₀ he) q).choose
    have ha:(QuotientAddGroup.mk' (latticeKernel L p cov e₀ he)) a=q:=
      (QuotientAddGroup.mk'_surjective (latticeKernel L p cov e₀ he) q).choose_spec
    change (QuotientAddGroup.mk' (latticeKernel L p cov e₀ he))
      (fiberMap_surjective L p cov e₀ he (fiberMap L p cov e₀ he a)).choose=q
    exact ((quotient_fiber L p cov e₀ he _ _).mpr
      (fiberMap_surjective L p cov e₀ he (fiberMap L p cov e₀ he a)).choose_spec).trans ha
  right_inv e:=by
    have h:=(QuotientAddGroup.mk'_surjective (latticeKernel L p cov e₀ he)
      ((QuotientAddGroup.mk' (latticeKernel L p cov e₀ he))
        (fiberMap_surjective L p cov e₀ he e).choose)).choose_spec
    exact ((quotient_fiber L p cov e₀ he _ _).mp h).trans
      (fiberMap_surjective L p cov e₀ he e).choose_spec

lemma fiberEquiv_mk (a:L) :
    fiberEquiv L p cov e₀ he ((QuotientAddGroup.mk' (latticeKernel L p cov e₀ he)) a)=
      fiberMap L p cov e₀ he a :=
  (quotient_fiber L p cov e₀ he _ _).mp
    (QuotientAddGroup.mk'_surjective (latticeKernel L p cov e₀ he) _).choose_spec

/-- The integer index is consumed only AFTER identifying the quotient
with the actual complete fiber of the original covering map. -/
theorem index_eq_fiber : (latticeKernel L p cov e₀ he).index=Nat.card (Fiber L p) := by
  rw [AddSubgroup.index_eq_card]
  exact Nat.card_congr (fiberEquiv L p cov e₀ he)

/-- Translation by a TARGET period is the actual action on the zero
fiber induced by z ↦ z+a upstairs. This formula fixes the action without
assuming an unrelated group law on the original cover. -/
@[expose] def fiberTranslate (a:L) : Fiber L p≃Fiber L p where
  toFun e:=fiberEquiv L p cov e₀ he
    ((fiberEquiv L p cov e₀ he).symm e+
      (QuotientAddGroup.mk' (latticeKernel L p cov e₀ he)) a)
  invFun e:=fiberEquiv L p cov e₀ he
    ((fiberEquiv L p cov e₀ he).symm e-
      (QuotientAddGroup.mk' (latticeKernel L p cov e₀ he)) a)
  left_inv e:=by simp
  right_inv e:=by simp
lemma fiberTranslate_lift (a b:L) :
    fiberTranslate L p cov e₀ he a (fiberMap L p cov e₀ he b)=
      fiberMap L p cov e₀ he (b+a) := by
  change fiberEquiv L p cov e₀ he
    ((fiberEquiv L p cov e₀ he).symm (fiberMap L p cov e₀ he b)+
      (QuotientAddGroup.mk' (latticeKernel L p cov e₀ he)) a)=_
  rw [←fiberEquiv_mk L p cov e₀ he b,Equiv.symm_apply_apply,←map_add,fiberEquiv_mk]
end ComplexTorusCoverIndex318
