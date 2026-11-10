module
public import ContactWholeChartRestrictionInjective318
public section
noncomputable section
namespace ContactOriginalLineSectionsFinite318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalLineBothCharts318 ContactOriginalWholeRestriction318
open ContactWholeOpenSectionRestriction318 ContactOriginalRestrictionCoordinates318
open ContactOriginalLaurentCoordinates318 ContactOriginalCohomologyCoordinates318
open LaurentVectorFiltration318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- Original global sections carry the Q action of their actual structural
coefficient ring, independently of the Laurent coordinate map below. -/
instance : Module ℚ Γ(L.object,⊤) :=
  OriginalLineRationalCohomology318.sectionModule (ContactIntrinsicDifferentials318.structureMap c) L ⊤

/-- Restrict the SAME original global section to the FULL overlap and use
the already proved original overlap coordinates. -/
def globalCoordinates : Γ(L.object,⊤) →+ V ℚ (finiteRank c L) :=
  (overlapCoordinates c L).toAddMonoidHom.comp
    (L.object.presheaf.map (homOfLE (show finiteOpen c ⊓ infinityOpen c ≤ ⊤ from le_top)).op).hom

lemma finite_formula (s : Γ(L.object,⊤)) : globalCoordinates c L s =
    coordinates c L (finiteRestriction c L ((finiteSectionsEquiv c L).symm
      (L.object.presheaf.map (homOfLE (show finiteOpen c ≤ ⊤ from le_top)).op s))) := by
  rw [← ContactOriginalCohomologyCoordinates318.finite_res]
  change overlapCoordinates c L (L.object.presheaf.map _ s) =
    overlapCoordinates c L (L.object.presheaf.map _ (L.object.presheaf.map _ s))
  rw [← Functor.map_comp_apply] <;> rfl

lemma infinity_formula (s : Γ(L.object,⊤)) : globalCoordinates c L s =
    coordinates c L (infinityRestriction c L ((infinitySectionsEquiv c L).symm
      (L.object.presheaf.map (homOfLE (show infinityOpen c ≤ ⊤ from le_top)).op s))) := by
  rw [← ContactOriginalCohomologyCoordinates318.infinity_res]
  change overlapCoordinates c L (L.object.presheaf.map _ s) =
    overlapCoordinates c L (L.object.presheaf.map _ (L.object.presheaf.map _ s))
  rw [← Functor.map_comp_apply] <;> rfl

/-- Every actual global section lands in the matching-vector space of the
SAME actual transition; both memberships come from original restrictions. -/
lemma matching (s : Γ(L.object,⊤)) : globalCoordinates c L s ∈
    positive ⊓ negative.map (LaurentTransitionBounds318.underlying (transition c L)) := by
  constructor
  · rw [finite_formula,← ContactOriginalRestrictionCoordinates318.finite_image c L]
    exact ⟨_,rfl⟩
  · rw [ContactOriginalLaurentBoundary318.negative_image,infinity_formula,
      ← ContactOriginalRestrictionCoordinates318.infinity_image c L]
    exact ⟨_,rfl⟩

def matchingLinear : Γ(L.object,⊤) →ₗ[ℚ] LaurentCechSectionsFinite318.H0 (transition c L) :=
  (globalCoordinates c L).toRatLinearMap.codRestrict _ (matching c L)

lemma matching_injective : Function.Injective (matchingLinear c L) := by
  intro s t h
  apply ContactWholeChartRestrictionInjective318.global_injective c L
  apply (overlapCoordinates c L).injective
  exact congrArg Subtype.val h

/-- Finite-dimensionality of the literal original GLOBAL section module,
not just of a related coordinate matching space. -/
instance finite_sections : FiniteDimensional ℚ Γ(L.object,⊤) := by
  letI := coordinate_h0_finite c L
  exact FiniteDimensional.of_injective (matchingLinear c L) (matching_injective c L)
end ContactOriginalLineSectionsFinite318
