module
public import OriginalAffineSectionZero318
public section
noncomputable section
namespace SectionZeroEquivalence318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  (Q : Type w) [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q) (s : P)

/-- The actual section evaluation ideal is invariant under a SPECIFIED
linear isomorphism carrying the section. No basis or radical is chosen. -/
lemma ideal : ProjectiveSectionIdeal318.ideal R Q (e s) = ProjectiveSectionIdeal318.ideal R P s := by
  apply le_antisymm
  · rintro a ⟨φ,rfl⟩
    exact ⟨φ.comp e.toLinearMap,rfl⟩
  · rintro a ⟨φ,rfl⟩
    refine ⟨φ.comp e.symm.toLinearMap,?_⟩
    change φ (e.symm (e s))=φ s
    rw [LinearEquiv.symm_apply_apply]

variable (A : CommRingCat.{u}) (L N : Line (Spec A)) (a : L.object ≅ N.object)

lemma original_affine (s : OriginalLineAffineModel318.sections A L) :
    OriginalAffineSectionZero318.ideal A N (moduleSpecΓFunctor.map a.hom s) =
      OriginalAffineSectionZero318.ideal A L s :=
  ideal A _ _ (moduleSpecΓFunctor.mapIso a).toLinearEquiv s
end SectionZeroEquivalence318
