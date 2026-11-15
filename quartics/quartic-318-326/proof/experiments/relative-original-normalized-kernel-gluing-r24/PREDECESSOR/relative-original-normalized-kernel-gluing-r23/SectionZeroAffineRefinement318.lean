module
public import OriginalAffineSectionZero318
public import OriginalAffinePathWholeSections318
public import OriginalSectionPullbackComposition318
public import AffineQuotientPullback318
public section
noncomputable section
namespace SectionZeroAffineRefinement318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open OriginalSectionPullbackComposition318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Z : Scheme.{u}} (A B : CommRingCat.{u}) (j : Spec A ⟶ X)
  (f : A ⟶ B) (L : Line X) (s : Γ(L.object,⊤))

/-- Literal evaluation ideal of the ACTUAL geometric section pullback. -/
abbrev sectionIdeal := OriginalAffineSectionZero318.ideal A
  (LineSheafPullback318.line j L) (pull j L.object s)

@[expose] def comparison : (Scheme.Modules.pullback (Spec.map f)).obj
    (LineSheafPullback318.line j L).object ≅
    (LineSheafPullback318.line (Spec.map f ≫ j) L).object :=
  (Scheme.Modules.pullbackComp (Spec.map f) j).app L.object

lemma section_unit : OriginalAffineLinePathSections318.restriction f
    (LineSheafPullback318.line j L) (LineSheafPullback318.line (Spec.map f ≫ j) L)
    (comparison A B j f L) (pull j L.object s) = pull (Spec.map f ≫ j) L.object s := by
  rw [OriginalAffinePathWholeSections318.restriction_direct]
  exact OriginalSectionPullbackComposition318.composition (Spec.map f) j L.object s

/-- Base change of the original section ideal follows the actual
pullback associator and unit, including arbitrary nonflat affine changes. -/
lemma ideal_map : sectionIdeal B (Spec.map f ≫ j) L s =
    Ideal.map f.hom (sectionIdeal A j L s) := by
  have h := OriginalAffineSectionZero318.along_path f
    (LineSheafPullback318.line j L) (LineSheafPullback318.line (Spec.map f ≫ j) L)
    (comparison A B j f L) (pull j L.object s)
  rw [section_unit] at h
  exact h

variable (p : Z ⟶ X)
  (k : Spec (CommRingCat.of (A⧸sectionIdeal A j L s)) ⟶ Z)
  (hs : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (sectionIdeal A j L s)))) k j p)

@[expose] def into : Spec (CommRingCat.of (B⧸sectionIdeal B (Spec.map f ≫ j) L s)) ⟶ Z :=
  Spec.map (AffineQuotientPullback318.arrow f (sectionIdeal A j L s)
    (sectionIdeal B (Spec.map f ≫ j) L s) (ideal_map A B j f L s)) ≫ k

/-- Every affine refinement has the genuine zero quotient of its OWN
actual geometric section, Cartesian over the SAME global zero map.
No assumed equality between an arbitrary coordinate and the section. -/
lemma square : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (sectionIdeal B (Spec.map f ≫ j) L s))))
    (into A B j f L s k) (Spec.map f ≫ j) p :=
  (AffineQuotientPullback318.pullback_square f (sectionIdeal A j L s)
    (sectionIdeal B (Spec.map f ≫ j) L s) (ideal_map A B j f L s)).paste_vert hs
/-- Relabeling equal quotient ideals keeps the actual quotient morphism. -/
@[expose] def transportInto {I J : Ideal A} (h : I=J)
    (k : Spec (CommRingCat.of (A⧸I)) ⟶ Z) : Spec (CommRingCat.of (A⧸J)) ⟶ Z :=
  (eqToIso (congrArg (fun Q : Ideal A => Spec (CommRingCat.of (A⧸Q))) h.symm)).hom ≫ k

lemma transport_square {I J : Ideal A} (h : I=J)
    (k : Spec (CommRingCat.of (A⧸I)) ⟶ Z)
    (hI : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) k j p) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
      (transportInto A h k) j p := by
  subst J
  simpa only [transportInto,eqToIso_refl,Category.id_comp] using hI
end SectionZeroAffineRefinement318
