module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public section
noncomputable section
namespace LatticeQuotientKernel318
variable {V : Type*} [AddCommGroup V] (L : AddSubgroup V) (F : V ≃+ V)
  (h : ∀ x∈L,F x∈L)
@[expose] def induced : V ⧸ L →+ V ⧸ L :=
  QuotientAddGroup.map L L F.toAddMonoidHom h
@[expose] def lattice : L →+ L where
  toFun x := ⟨F x.val,h x.val x.property⟩
  map_zero' := Subtype.ext (map_zero F)
  map_add' x y := Subtype.ext (map_add F x.val y.val)
@[expose] def rootHom : L →+ (induced L F h).ker where
  toFun x := ⟨QuotientAddGroup.mk' L (F.symm x.val),by
    change QuotientAddGroup.mk' L (F (F.symm x.val))=0
    rw [F.apply_symm_apply]
    exact (QuotientAddGroup.eq_zero_iff _).mpr x.property⟩
  map_zero' := by apply Subtype.ext; simp only [map_zero]
  map_add' x y := by apply Subtype.ext; simp only [map_add]
lemma root_surjective : Function.Surjective (rootHom L F h) := by
  intro q
  obtain ⟨z,hz⟩ := Quotient.exists_rep q.val
  change QuotientAddGroup.mk' L z=q.val at hz
  have hF : F z∈L := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change induced L F h (QuotientAddGroup.mk' L z)=0
    rw [hz]
    exact q.property
  refine ⟨⟨F z,hF⟩,?_⟩
  apply Subtype.ext
  change QuotientAddGroup.mk' L (F.symm (F z))=q.val
  rw [F.symm_apply_apply]
  exact hz
lemma root_kernel : (rootHom L F h).ker=(lattice L F h).range := by
  ext x
  change rootHom L F h x=0 ↔ ∃ y,lattice L F h y=x
  constructor
  · intro hx
    have hv := congrArg Subtype.val hx
    change QuotientAddGroup.mk' L (F.symm x.val)=0 at hv
    refine ⟨⟨F.symm x.val,(QuotientAddGroup.eq_zero_iff _).mp hv⟩,?_⟩
    apply Subtype.ext
    exact F.apply_symm_apply x.val
  · rintro ⟨y,hy⟩
    rw [←hy]
    apply Subtype.ext
    change QuotientAddGroup.mk' L (F.symm (F y.val))=0
    rw [F.symm_apply_apply]
    exact (QuotientAddGroup.eq_zero_iff _).mpr y.property
/-- The whole quotient-group kernel is the actual lattice quotient by
its full image, not by a chosen finite-index substitute. -/
@[expose] def equivalence : L ⧸ (lattice L F h).range ≃+ (induced L F h).ker :=
  (QuotientAddGroup.quotientAddEquivOfEq (root_kernel L F h).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (rootHom L F h) (root_surjective L F h))
end LatticeQuotientKernel318
