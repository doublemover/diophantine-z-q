module
public import ActualTwoDescentOriginalSquareAmbientAtlas318
public section
noncomputable section
namespace ActualTwoDescentOriginalSquareLocalData318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIdealOpenFrameCover318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentOriginalMatchedSquareIsomorphisms318
open ActualTwoDescentOriginalSquareAmbientAtlas318 ActualTwoDescentOpenChartAmbientCoordinates318
open ActualTwoDescentOpenChartCoordinateNaturality318 ActualTwoDescentOpenChartRefinementCoordinates318
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Actual OLD chart square coordinates on the original ambient opens.
Compatibility is produced from the complete old overlap identities. -/
def squareLocalData (n : K) (i : Fin 3) :
    ModuleLocalGluing318.LocalData (squareModule n i)
      (SheafOfModules.unit (originalCubicScheme n).ringCatSheaf) (opens n i) where
  map a V hV := coordinate (embedding n i a.down) (squareModule n i) (chartSquare n i a.down).hom V hV
  natural a V W hV hW s := coordinate_natural (embedding n i a.down)
    (squareModule n i) (chartSquare n i a.down).hom V W hV hW s
  compatible a b V ha hb s := by
    by_cases he : a.down=b.down
    · cases a; cases b
      cases he
      rfl
    · have hV : V≤(overlapEmbedding n).opensRange := by
        rw [←actual_distinct_intersection n i a.down b.down he]
        exact le_inf ha hb
      have hA := coordinate_refinement (refinement n i a.down) (embedding n i a.down)
        (overlapEmbedding n) (refinement_square n i a.down) (squareModule n i)
        (chartSquare n i a.down).hom V hV ha s
      have hB := coordinate_refinement (refinement n i b.down) (embedding n i b.down)
        (overlapEmbedding n) (refinement_square n i b.down) (squareModule n i)
        (chartSquare n i b.down).hom V hV hb s
      rw [actual_chart_square_refinement] at hA hB
      exact hA.symm.trans hB

lemma squareLocalData_bijective (n : K) (i : Fin 3) (a : ULift.{u} (Option Bool))
    (V : (originalCubicScheme n).Opens) (hV : V≤opens n i a) :
    Function.Bijective ((squareLocalData n i).map a V hV) :=
  coordinate_bijective (embedding n i a.down) (squareModule n i) (chartSquare n i a.down).hom V hV
end ActualTwoDescentOriginalSquareLocalData318
