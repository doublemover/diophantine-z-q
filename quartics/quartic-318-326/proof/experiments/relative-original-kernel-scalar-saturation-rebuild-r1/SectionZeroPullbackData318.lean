module
public import SectionZeroPullbackChart318
public section
noncomputable section
namespace SectionZeroPullbackData318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
universe u
variable {Z X W Y : Scheme.{u}} (p : Z ⟶ X) (q : W ⟶ Y)
  (t : W ⟶ Z) (g : Y ⟶ X) (F : IsPullback t q p g)
  (L : Line X) (s : Γ(L.object,⊤)) (D : SectionZeroChartData318.Data p L s)
/-- Whole original section-zero charts survive arbitrary geometric
pullback, with no flatness assumptions. Cartier regularity is separate. -/
@[expose] def data : SectionZeroChartData318.Data q (LineSheafPullback318.line g L)
    (OriginalSectionPullbackComposition318.pull g L.object s) where
  Index := SectionZeroPullbackCover318.index p L s D g
  ring := SectionZeroPullbackCover318.ring p L s D g
  into := SectionZeroPullbackCover318.into p L s D g
  open_into _ := inferInstance
  cover := SectionZeroPullbackCover318.covers p L s D g
  zero := SectionZeroPullbackChart318.into p q t g F L s D
  cartesian := SectionZeroPullbackChart318.cartesian p q t g F L s D
end SectionZeroPullbackData318
