module
public import PELOriginalCotangentSectionGerms318
public import FiniteClosedSupportSections318
public section
noncomputable section
namespace PELOriginalCotangentSkyscrapers318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat Opposite
open PELOriginalCommonContactBase318 FourRootGluedDerivativeIdeal318
open PELOriginalCotangentSectionGerms318
/-- The underlying additive sheaf of the SAME intrinsic relative cotangent. -/
@[expose] def additiveSheaf : Sheaf Ab X := ⟨omega.presheaf,omega.isSheaf⟩
lemma support_point_closed (z : zeroScheme branches) :
    IsClosed ({into branches z} : Set X) := by
  have h := (into branches).isClosedEmbedding.isClosedMap _
    (FourRootZeroAllPoints318.point_closed branches branches_injective z)
  simpa only [Set.image_singleton] using h
lemma outside_isZero (x : X) (hx : x ∉ Set.range (into branches)) :
    IsZero (additiveSheaf.obj.stalk x) := by
  letI := outside_subsingleton x hx
  rw [IsZero.iff_id_eq_zero]
  ext a
  exact Subsingleton.elim _ _
/-- Actual sheaf decomposition into the40 genuine skyscraper stalks.
No frame, trivialization or identification of Ω with O_Z is asserted. -/
@[expose] def sheafIso : additiveSheaf ≅
    ∏ᶜ FiniteClosedSupportSheaf318.pieces additiveSheaf (into branches) := by
  haveI := FiniteClosedSupportSheaf318.toPieces_isIso additiveSheaf (into branches)
    (into branches).isClosedEmbedding.injective support_point_closed outside_isZero
  exact asIso (FiniteClosedSupportSheaf318.toPieces additiveSheaf (into branches))
/-- Actual global relative-cotangent sections, canonically mapped to their
stalks at all zero-scheme points. Its components are the literal germs. -/
@[expose] def globalSectionsIso : additiveSheaf.obj.obj (op ⊤) ≅
    ∏ᶜ fun z : zeroScheme branches => additiveSheaf.obj.stalk (into branches z) := by
  haveI := FiniteClosedSupportSections318.globalGerms_isIso additiveSheaf (into branches)
    (into branches).isClosedEmbedding.injective support_point_closed outside_isZero
  exact asIso (FiniteClosedSupportSections318.globalGerms additiveSheaf (into branches))
lemma globalSectionsIso_hom_π (z : zeroScheme branches) :
    globalSectionsIso.hom ≫ Pi.π _ z = omega.presheaf.germ ⊤ (into branches z) trivial :=
  Pi.lift_π _ _
end PELOriginalCotangentSkyscrapers318
