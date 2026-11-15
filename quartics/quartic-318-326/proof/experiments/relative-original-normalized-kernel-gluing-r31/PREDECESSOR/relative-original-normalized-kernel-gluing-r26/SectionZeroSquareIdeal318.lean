module
public import SectionZeroChartData318
public section
noncomputable section
namespace SectionZeroSquareIdeal318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSectionPullbackComposition318 SectionZeroAffineRefinement318
universe u
variable {X Y : Scheme.{u}} (g : Y ⟶ X) (A B : CommRingCat.{u})
  (φ : A ⟶ B) (j : Spec A ⟶ X) (k : Spec B ⟶ Y)
  (h : Spec.map φ ≫ j=k ≫ g) (L : Line X) (s : Γ(L.object,⊤))
include h in
lemma section : OriginalCoefficientChartLine318.originalRestriction g φ j k h L
    (pull j L.object s)=pull k ((LineSheafPullback318.line g L).object) (pull g L.object s) := by
  rw [OriginalCoefficientChartLine318.originalRestriction,OriginalAffinePathWholeSections318.restriction_direct]
  exact OriginalSectionPullbackComposition318.square (Spec.map φ) j k g h L.object s
include h in
/-- Full section-zero ideals follow an arbitrary actual affine square
for the geometric pullback section, not a selected matching coordinate. -/
lemma ideal : sectionIdeal B k (LineSheafPullback318.line g L) (pull g L.object s)=
    Ideal.map φ.hom (sectionIdeal A j L s) := by
  have he := OriginalAffineSectionZero318.original_pullback g φ j k h L (pull j L.object s)
  rw [section g A B φ j k h L s] at he
  exact he
end SectionZeroSquareIdeal318
