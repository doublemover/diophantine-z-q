module
public import RelativeCoefficientChange318
public import OriginalAffineLinePathSections318
public import PullbackPathComposition318
public section
noncomputable section
namespace OriginalCoefficientChartLine318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
  {A B : CommRingCat.{u}} (f : A ⟶ B) (j : Spec A ⟶ X) (k : Spec B ⟶ Y)
  (h : Spec.map f ≫ j = k ≫ p) (L : Line X)

/-- Actual geometric path comparison. Its endpoint is the restriction
of the SAME pulled-back global line, not an isomorphic replacement line. -/
@[expose] def sheafComparison :
    (Scheme.Modules.pullback (Spec.map f)).obj (LineSheafPullback318.line j L).object ≅
      (LineSheafPullback318.line k (LineSheafPullback318.line p L)).object :=
  (Scheme.Modules.pullbackComp (Spec.map f) j).app L.object ≪≫
    (Scheme.Modules.pullbackCongr h).app L.object ≪≫
    ((Scheme.Modules.pullbackComp k p).app L.object).symm

/-- Canonical affine-section extension, still over the actual original
chart-ring map. Coefficient-only tensor cancellation is a separate step. -/
@[expose] def sectionsComparison :
    (ModuleCat.extendScalars f.hom).obj
      (OriginalLineAffineModel318.sections A (LineSheafPullback318.line j L)) ≅
    OriginalLineAffineModel318.sections B
      (LineSheafPullback318.line k (LineSheafPullback318.line p L)) :=
  OriginalAffineLinePathSections318.comparison f _ _ (sheafComparison p f j k h L)

@[expose] def originalRestriction := OriginalAffineLinePathSections318.restriction
  f (LineSheafPullback318.line j L)
    (LineSheafPullback318.line k (LineSheafPullback318.line p L))
      (sheafComparison p f j k h L)

lemma unit (m : OriginalLineAffineModel318.sections A (LineSheafPullback318.line j L)) :
    (sectionsComparison p f j k h L).hom
      ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app _ m) =
        originalRestriction p f j k h L m :=
  OriginalAffineLinePathSections318.unit_apply _ _ _ _ m

lemma scalar (a : A)
    (m : OriginalLineAffineModel318.sections A (LineSheafPullback318.line j L)) :
    originalRestriction p f j k h L (a • m) =
      f.hom a • originalRestriction p f j k h L m :=
  OriginalAffineLinePathSections318.restriction_smul _ _ _ _ a m
end OriginalCoefficientChartLine318
