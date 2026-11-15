module
public import ContactNormalizedParameterCompact318
public section
noncomputable section
namespace ContactNormalizedAbsoluteAmbient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "q" => ContactRelativeStructuralHOne318.projection R c
local notation "b" => ContactNormalizedSectionParameter318.projection R c L hz
abbrev base : ContactNormalizedSectionParameter318.scheme R c L hz ⟶ Spec (CommRingCat.of ℚ) := b ≫ baseMap R
abbrev original : ContactNormalizedGlobalClosedFamily318.ambient R c L hz ⟶ ContactGlobalSmooth318.Model c :=
  pullback.fst q b ≫ pullback.fst p (baseMap R)
lemma cartesian : IsPullback (original R c L hz) (pullback.snd q b) p (base R c L hz) :=
  ((IsPullback.of_hasPullback q b).flip.paste_vert (IsPullback.of_hasPullback p (baseMap R)).flip).flip
/-- The SAME normalized original curve is the actual absolute p-first
family over the complete parameter scheme, with both projections fixed. -/
@[expose] def comparison : ContactNormalizedGlobalClosedFamily318.ambient R c L hz ≅
    pullback p (base R c L hz) := (cartesian R c L hz).isoPullback
@[reassoc] lemma original_projection : (comparison R c L hz).hom ≫ pullback.fst p (base R c L hz)=original R c L hz :=
  (cartesian R c L hz).isoPullback_hom_fst
@[reassoc] lemma base_projection : (comparison R c L hz).hom ≫ pullback.snd p (base R c L hz)=pullback.snd q b :=
  (cartesian R c L hz).isoPullback_hom_snd
end ContactNormalizedAbsoluteAmbient318
