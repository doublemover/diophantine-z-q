module
public import ContactOverlapTensorCharts318
public import OriginalAffineMapSections318

public section
noncomputable section
namespace ContactOriginalModuleOverlap318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalLaurentOverlap318 ContactOriginalLineBothCharts318
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

abbrev finiteMap := OriginalAffineMapSections318.ringMap (finiteEdge c)
abbrev infinityMap := OriginalAffineMapSections318.ringMap (infinityEdge c)

/-- The exact original finite-chart section module after actual overlap
scalar extension, not an unrelated module of matching dimension. -/
abbrev finiteModule := OriginalLineAffineBaseChange318.extendedSections
  (finiteMap c) (finiteLine c L)
abbrev infinityModule := OriginalLineAffineBaseChange318.extendedSections
  (infinityMap c) (infinityLine c L)

def finiteComparison := OriginalAffineMapSections318.sectionsIso (finiteEdge c) (finiteLine c L)
def infinityComparison := OriginalAffineMapSections318.sectionsIso (infinityEdge c) (infinityLine c L)

/-- Global sections of the very same geometric infinity-to-finite overlap
isomorphism along the actual affine inverse comparison. -/
def actualSectionTransition := moduleSpecΓFunctor.mapIso
  ((Scheme.Modules.pullback (scheme c).isoSpec.inv).mapIso (ContactOriginalLineOverlap318.transition c L))

lemma actualSectionTransition_eq : actualSectionTransition c L =
    ContactOriginalLineOverlap318.sectionTransition c L := by
  simp only [actualSectionTransition,ContactOriginalLineOverlap318.sectionTransition,
    ContactOriginalLineOverlap318.fromSpec,IsAffineOpen.fromSpec_top]

/-- The original geometric overlap now compares scalar extensions of the
OLD original section modules themselves. -/
def transition : infinityModule c L ≅ finiteModule c L :=
  infinityComparison c L ≪≫ actualSectionTransition c L ≪≫ (finiteComparison c L).symm

/-- The original sheaf-induced overlap map is recovered exactly under the
original affine section comparisons. -/
@[reassoc] lemma transition_recovery : (transition c L).hom ≫ (finiteComparison c L).hom =
    (infinityComparison c L).hom ≫ (actualSectionTransition c L).hom := by
  simp only [transition,Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]

lemma finite_map_spec : Spec.map (finiteMap c) = (scheme c).isoSpec.inv ≫ finiteEdge c :=
  OriginalAffineMapSections318.specMap (finiteEdge c)
lemma infinity_map_spec : Spec.map (infinityMap c) = (scheme c).isoSpec.inv ≫ infinityEdge c :=
  OriginalAffineMapSections318.specMap (infinityEdge c)
end ContactOriginalModuleOverlap318
