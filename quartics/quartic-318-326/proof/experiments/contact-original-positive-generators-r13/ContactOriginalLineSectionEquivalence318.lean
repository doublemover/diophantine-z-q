module
public import ContactOriginalLineCohomologyFinite318
public import OriginalModuleTwoOpenGluing318
public section
noncomputable section
namespace ContactOriginalLineSectionEquivalence318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalLineBothCharts318 ContactOriginalWholeRestriction318
open ContactWholeOpenSectionRestriction318 ContactOriginalRestrictionCoordinates318
open ContactOriginalLaurentCoordinates318 ContactOriginalCohomologyCoordinates318
open ContactOriginalLineSectionsFinite318 LaurentVectorFiltration318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- Every actual matching vector comes from a genuine original global
section, obtained by gluing the SAME two whole-chart representatives. -/
lemma matching_surjective : Function.Surjective (matchingLinear c L) := by
  intro v
  have hx := v.property.1
  have hy := v.property.2
  rw [ContactOriginalLaurentBoundary318.negative_image] at hy
  rw [← finite_image c L] at hx
  rw [← infinity_image c L] at hy
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  have hab : L.object.presheaf.map (homOfLE inf_le_left :
      finiteOpen c ⊓ infinityOpen c ⟶ finiteOpen c).op (finiteSectionsEquiv c L a) =
    L.object.presheaf.map (homOfLE inf_le_right :
      finiteOpen c ⊓ infinityOpen c ⟶ infinityOpen c).op (infinitySectionsEquiv c L b) := by
    apply (overlapCoordinates c L).injective
    rw [finite_res,infinity_res,AddEquiv.symm_apply_apply,AddEquiv.symm_apply_apply,ha,hb]
  obtain ⟨s,hs,ht⟩ := OriginalModuleTwoOpenGluing318.exists_gluing L.object
    (finiteOpen c) (infinityOpen c) (cover c)
    (finiteSectionsEquiv c L a) (infinitySectionsEquiv c L b) hab
  refine ⟨s,?_⟩
  apply Subtype.ext
  change globalCoordinates c L s = v.val
  rw [ContactOriginalLineSectionsFinite318.finite_formula,hs,AddEquiv.symm_apply_apply]
  exact ha

/-- Exact original global sections = the actual Laurent matching space.
The map is literal full-overlap restriction and its proved coordinates;
surjectivity is original sheaf gluing, not a dimension comparison. -/
def equivalence : Γ(L.object,⊤) ≃ₗ[ℚ] LaurentCechSectionsFinite318.H0 (transition c L) :=
  LinearEquiv.ofBijective (matchingLinear c L)
    ⟨matching_injective c L,matching_surjective c L⟩

lemma equivalence_overlap (s : Γ(L.object,⊤)) :
    (equivalence c L s).val = overlapCoordinates c L
      (L.object.presheaf.map (homOfLE (show finiteOpen c ⊓ infinityOpen c ≤ ⊤ from le_top)).op s) := rfl

lemma finrank_sections : Module.finrank ℚ Γ(L.object,⊤) =
    Module.finrank ℚ (LaurentCechSectionsFinite318.H0 (transition c L)) :=
  (equivalence c L).finrank_eq
end ContactOriginalLineSectionEquivalence318
