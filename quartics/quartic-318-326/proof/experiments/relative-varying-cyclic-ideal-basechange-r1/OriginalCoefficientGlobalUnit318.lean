module
public import OriginalCoefficientChartLine318
public import OriginalAffinePathWholeSections318
public import OriginalSectionPullbackComposition318
public section
noncomputable section
namespace OriginalCoefficientGlobalUnit318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSectionPullbackComposition318
universe u
variable {X Y : Scheme.{u}} (p : Y ⟶ X) {A B : CommRingCat.{u}}
  (f : A ⟶ B) (j : Spec A ⟶ X) (k : Spec B ⟶ Y)
  (h : Spec.map f ≫ j = k ≫ p) (L : Line X)

/-- Restricting an original GLOBAL section then changing coefficients
is the genuine global geometric pullback then chart restriction, with the
actual original path comparison retained. No H0 presentation is used. -/
lemma square (s : Γ(L.object,⊤)) :
    OriginalCoefficientChartLine318.originalRestriction p f j k h L (pull j L.object s) =
      pull k ((Scheme.Modules.pullback p).obj L.object) (pull p L.object s) := by
  rw [show OriginalCoefficientChartLine318.originalRestriction p f j k h L (pull j L.object s) =
    (OriginalCoefficientChartLine318.sheafComparison p f j k h L).hom.app ⊤
      (pull (Spec.map f) ((Scheme.Modules.pullback j).obj L.object) (pull j L.object s)) from
        OriginalAffinePathWholeSections318.restriction_direct _ _ _ _ _]
  exact OriginalSectionPullbackComposition318.square (Spec.map f) j k p h L.object s
end OriginalCoefficientGlobalUnit318
