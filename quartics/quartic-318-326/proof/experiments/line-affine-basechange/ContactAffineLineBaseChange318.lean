module
public import OriginalLineAffineBaseChange318
public import SourceGlobalAffine318
public import ContactGlobalSmooth318
public import LineClassPullbackLaws318
public section
noncomputable section
namespace ContactAffineLineBaseChange318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
abbrev X := ContactGlobalSmooth318.Model c
abbrev R := CommRingCat.of (ContactKummerOrder318.SourceOrder c)
abbrev j := SourceGlobalAffine318.chartEmbedding c
abbrev chartLine (L : Line (X c)) := LineSheafPullback318.line (j c) L

variable {S : CommRingCat} (f : R c ⟶ S) (L : Line (X c))
/-- Scalar extension of the literal sections of the original source line
on its actual full affine source chart. -/
abbrev extendedSections :=
  OriginalLineAffineBaseChange318.extendedSections f (chartLine c L)

/-- The comparison lands in the actual original source-line pullback
along the composite original scheme map, via the original pullback
composition isomorphism. No alternate source model is substituted. -/
@[expose] def sourcePullbackIso : tilde (extendedSections c f L) ≅
    (LineSheafPullback318.line (Spec.map f ≫ j c) L).object :=
  OriginalLineAffineBaseChange318.sheafIso f (chartLine c L) ≪≫
    LineClassPullbackLaws318.compositionIso (Spec.map f) (j c) L

@[expose] def sourceSectionsIso : extendedSections c f L ≅
    OriginalLineAffineModel318.sections S
      (LineSheafPullback318.line (Spec.map f ≫ j c) L) :=
  tilde.isoTop (extendedSections c f L) ≪≫ moduleSpecΓFunctor.mapIso (sourcePullbackIso c f L)

lemma sourcePullbackIso_hom : (sourcePullbackIso c f L).hom =
    (OriginalLineAffineBaseChange318.sheafIso f (chartLine c L)).hom ≫
      (LineClassPullbackLaws318.compositionIso (Spec.map f) (j c) L).hom := rfl
end ContactAffineLineBaseChange318
