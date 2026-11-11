module
public import ProjectiveSectionIdeal318
public section
noncomputable section
namespace SectionZeroRegularCoordinate318
universe u v
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  (s : P)

@[expose] def sectionMap : R →ₗ[R] P where
  toFun a := a • s
  map_add' _ _ := add_smul _ _ _
  map_smul' a b := by simp [smul_smul]

/-- An intrinsic regular-section condition, defined before choosing a
rank-one frame. It is NOT supplied automatically for the universal section. -/
def Regular : Prop := Function.Injective (sectionMap R P s)

variable (e : P ≃ₗ[R] R)

lemma reconstruct : s = e s • e.symm 1 := by
  apply e.injective
  simp

/-- On any actual rank-one frame the same evaluation ideal is generated
by the literal coordinate of the original section, not by its radical. -/
lemma ideal_in_frame : ProjectiveSectionIdeal318.ideal R P s = Ideal.span {e s} := by
  apply le_antisymm
  · rintro a ⟨φ,rfl⟩
    rw [reconstruct R P s e,map_smul,smul_eq_mul]
    apply Ideal.mul_mem_right
    exact Ideal.subset_span (Set.mem_singleton _)
  · apply Ideal.span_le.mpr
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact ⟨e.toLinearMap,rfl⟩

/-- Exact Cartier-coordinate criterion. The non-zero-divisor condition
is equivalent to intrinsic injectivity, so changing the genuine line frame
cannot silently change the regular locus. -/
lemma regular_iff : Regular R P s ↔ ∀ a : R, a * e s=0 → a=0 := by
  constructor
  · intro h a ha
    apply h
    apply e.injective
    change e (a • s)=e (0 • s)
    simpa only [map_smul,smul_eq_mul,zero_mul] using ha
  · intro h a b hab
    have he := congrArg e hab
    change e (a • s)=e (b • s) at he
    simp only [map_smul,smul_eq_mul] at he
    apply sub_eq_zero.mp
    apply h (a-b)
    rw [sub_mul,he,sub_self]

lemma frame_independent (e' : P ≃ₗ[R] R) :
    (∀ a : R,a * e s=0 → a=0) ↔ (∀ a : R,a * e' s=0 → a=0) :=
  (regular_iff R P s e).symm.trans (regular_iff R P s e')
end SectionZeroRegularCoordinate318
