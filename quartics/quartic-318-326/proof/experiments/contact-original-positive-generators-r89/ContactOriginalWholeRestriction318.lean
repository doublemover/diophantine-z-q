module
public import ContactWholeOpenSectionRestriction318
import all ContactWholeOpenSectionRestriction318
import all ContactOriginalRestrictionCoordinates318
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
    finiteRestriction c L m = finiteDirect c L m := by
  dsimp only [finiteRestriction, finiteDirect]
  exact OriginalTensorChartWholeRestriction318.original_restriction
    (CommRingCat.of (Polynomial ℚ)) (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
    (CommRingCat.of (ContactKummerOrder318.SourceOrder c))
    (projection c) (finiteEdge c) (ContactOverlapTensorCharts318.finiteIso c).symm
    (ContactOverlapTensorCharts318.finiteIso_inv_base c)
    (ContactOverlapTensorCharts318.finiteIso_inv_chart c)
    (finiteLine c L) (ContactOriginalLineOverlap318.line c L).object
    (ContactOriginalLineOverlap318.finiteComparison c L) m

lemma infinity_direct (m : infinitySections c L) :
    infinityRestriction c L m = infinityDirect c L m := by
  letI := OriginalLaurentProjectiveOverlap318.infinityHom.toAlgebra
  dsimp only [infinityRestriction, infinityDirect]
  exact OriginalTensorChartWholeRestriction318.original_restriction
    (CommRingCat.of (Polynomial ℚ)) (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
    (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c))
    (projection c) (infinityEdge c) (ContactOverlapTensorCharts318.infinityIso c).symm
    (ContactOverlapTensorCharts318.infinityIso_inv_base c)
    (ContactOverlapTensorCharts318.infinityIso_inv_chart c)
    (infinityLine c L) (ContactOriginalLineOverlap318.line c L).object
    (ContactOriginalLineOverlap318.infinityComparison c L) m

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

/-- Equality transport of the same presheaf restriction, proved before
specializing to the concrete original chart and its section. -/
private lemma image_restriction {X : Scheme} (M : X.Modules)
    (U V W : X.Opens) (h : U = V) (hUW : U ≤ W) (hVW : V ≤ W)
    (s : Γ(M,W)) :
    (M.presheaf.mapIso (eqToIso h.symm).op).addCommGroupIsoToAddEquiv
      (M.presheaf.map (homOfLE hUW).op s) =
        M.presheaf.map (homOfLE hVW).op s := by
  change M.presheaf.map _ (M.presheaf.map _ s) = _
  rw [← Functor.map_comp_apply]
  rfl

lemma finite_square (m : finiteSections c L) :
    overlapEquiv c L (finiteRestriction c L m) =
      L.object.presheaf.map (homOfLE inf_le_left :
        finiteOpen c ⊓ infinityOpen c ⟶ finiteOpen c).op (finiteSectionsEquiv c L m) := by
  have hs := congrArg
    (fun s : Γ(L.object,(into c) ''ᵁ ⊤) =>
      (L.object.presheaf.mapIso (eqToIso (overlap_image c).symm).op).addCommGroupIsoToAddEquiv s)
    (ContactWholeOpenSectionRestriction318.finite_square c L m)
  exact (congrArg (overlapEquiv c L) (finite_direct c L m)).trans
    (hs.trans (image_restriction L.object _ _ _ (overlap_image c) _
      inf_le_left (finiteSectionsEquiv c L m)))

lemma infinity_square (m : infinitySections c L) :
    overlapEquiv c L (infinityRestriction c L m) =
      L.object.presheaf.map (homOfLE inf_le_right :
        finiteOpen c ⊓ infinityOpen c ⟶ infinityOpen c).op (infinitySectionsEquiv c L m) := by
  have hs := congrArg
    (fun s : Γ(L.object,(into c) ''ᵁ ⊤) =>
      (L.object.presheaf.mapIso (eqToIso (overlap_image c).symm).op).addCommGroupIsoToAddEquiv s)
    (ContactWholeOpenSectionRestriction318.infinity_square c L m)
  exact (congrArg (overlapEquiv c L) (infinity_direct c L m)).trans
    (hs.trans (image_restriction L.object _ _ _ (overlap_image c) _
      inf_le_right (infinitySectionsEquiv c L m)))
end ContactOriginalWholeRestriction318
