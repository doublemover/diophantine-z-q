module
public import ContactWholeOpenSectionRestriction318
public import OriginalTensorChartWholeRestriction318
public section
noncomputable section
namespace ContactOriginalWholeRestriction318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open ContactOriginalLaurentOverlap318 ContactOriginalLineBothCharts318
open ContactWholeOpenSectionRestriction318 ContactOriginalRestrictionCoordinates318
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- The old tensor-recovered finite restriction IS the original direct
geometric restriction on the full overlap. -/
lemma finite_direct (m : finiteSections c L) :
    finiteRestriction c L m = finiteDirect c L m :=
  OriginalTensorChartWholeRestriction318.original_restriction _ _ _ _ _ _ _ _ _ _ _ m

lemma infinity_direct (m : infinitySections c L) :
    infinityRestriction c L m = infinityDirect c L m := by
  letI := OriginalLaurentProjectiveOverlap318.infinityHom.toAlgebra
  exact OriginalTensorChartWholeRestriction318.original_restriction _ _ _ _ _ _ _ _ _ _ _ m

abbrev finiteOpen := (SourceGlobalAffine318.chartEmbedding c) ''ᵁ ⊤
abbrev infinityOpen := (ContactWholeInfinityScheme318.into c) ''ᵁ ⊤

lemma overlap_image : (into c) ''ᵁ ⊤ = finiteOpen c ⊓ infinityOpen c := by
  simpa only [finiteOpen,infinityOpen,Scheme.Hom.image_top_eq_opensRange] using full_intersection c

lemma cover : finiteOpen c ⊔ infinityOpen c = ⊤ := by
  simpa only [finiteOpen,infinityOpen,Scheme.Hom.image_top_eq_opensRange] using whole_cover c

lemma finite_affine : IsAffineOpen (finiteOpen c) := by
  rw [finiteOpen,Scheme.Hom.image_top_eq_opensRange]
  exact isAffineOpen_opensRange _
lemma infinity_affine : IsAffineOpen (infinityOpen c) := by
  rw [infinityOpen,Scheme.Hom.image_top_eq_opensRange]
  exact isAffineOpen_opensRange _

/-- Exact original common Laurent module sections on the FULL original
ambient intersection, using the proved equality of its image with that
intersection. Only the actual original presheaf equality transport occurs. -/
def overlapEquiv : ContactCommonLaurentModule318.common c L ≃+
    Γ(L.object,finiteOpen c ⊓ infinityOpen c) :=
  (overlapSectionsEquiv c L).trans
    (L.object.presheaf.mapIso (eqToIso (overlap_image c).symm).op).addCommGroupIsoToAddEquiv

lemma finite_square (m : finiteSections c L) :
    overlapEquiv c L (finiteRestriction c L m) =
      L.object.presheaf.map (homOfLE inf_le_left :
        finiteOpen c ⊓ infinityOpen c ⟶ finiteOpen c).op (finiteSectionsEquiv c L m) := by
  rw [finite_direct]
  change L.object.presheaf.map _ (overlapSectionsEquiv c L (finiteDirect c L m)) = _
  rw [ContactWholeOpenSectionRestriction318.finite_square,← Functor.map_comp_apply] <;> rfl

lemma infinity_square (m : infinitySections c L) :
    overlapEquiv c L (infinityRestriction c L m) =
      L.object.presheaf.map (homOfLE inf_le_right :
        finiteOpen c ⊓ infinityOpen c ⟶ infinityOpen c).op (infinitySectionsEquiv c L m) := by
  rw [infinity_direct]
  change L.object.presheaf.map _ (overlapSectionsEquiv c L (infinityDirect c L m)) = _
  rw [ContactWholeOpenSectionRestriction318.infinity_square,← Functor.map_comp_apply] <;> rfl
end ContactOriginalWholeRestriction318
