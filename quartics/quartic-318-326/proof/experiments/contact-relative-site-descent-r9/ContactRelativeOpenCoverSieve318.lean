module
public import ContactRelativeFppfSieve318
public section
noncomputable section
namespace ContactRelativeOpenCoverSieve318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OriginalRelativeSite318 ContactUniversalRigidifiedClass318
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {Y : Scheme} (b : Y ⟶ FieldBase t) (R : Sieve (object b))
  (U : Y.OpenCover) (hR : ∀ i, R (arrow b (U.f i ≫ b) (U.f i) rfl))

include U hR in
/-- Any genuine open-immersion cover is admitted, not only a presentation
by literal open inclusions. The comparison uses each original image iso. -/
lemma mem_topology : R ∈ ContactRelativeOpenSieve318.topology t (object b) := by
  apply ContactRelativeOpenSieve318.mem_topology t b R (fun i => (U.f i).opensRange)
  · intro y hy
    obtain ⟨i,x,rfl⟩ := U.exists_eq y
    exact Opens.mem_iSup.mpr ⟨i,⟨x,rfl⟩⟩
  · intro i
    let a : openObject b (U.f i).opensRange ⟶ object (U.f i ≫ b) :=
      arrow (U.f i ≫ b) ((U.f i).opensRange.ι ≫ b) (U.f i).isoOpensRange.inv (by
        rw [← Category.assoc,Scheme.Hom.isoOpensRange_inv_comp])
    have ha : a ≫ arrow b (U.f i ≫ b) (U.f i) rfl = openArrow b (U.f i).opensRange := by
      ext
      exact Scheme.Hom.isoOpensRange_inv_comp (U.f i)
    rw [← ha]
    exact R.downward_closed (hR i) a
end ContactRelativeOpenCoverSieve318
