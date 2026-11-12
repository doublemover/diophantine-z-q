module
public import ActualTwoDescentOriginalSquareLocalData318
public section
noncomputable section
namespace ActualTwoDescentOriginalGlobalTensorSquare318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalIdealOpenFrameCover318 ActualTwoDescentOriginalSquareAmbientAtlas318
open ActualTwoDescentOriginalSquareLocalData318 ActualTwoDescentOpenChartAmbientCoordinates318
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The actual original global ideal sheaf has tensor square O.
This is a genuine native sheaf isomorphism. The inverse is separately
glued by the EXISTING ModuleLocalIsomorphism producer,not postulated. -/
def originalGlobalSquare (n : K) (hn : n≠0) (i : Fin 3) :
    IntrinsicTensorSheaf318.tensor (originalRootIdealSheaf n i) (originalRootIdealSheaf n i) ≅
      SheafOfModules.unit (originalCubicScheme n).ringCatSheaf :=
  ModuleLocalIsomorphism318.iso (squareLocalData n i) (actual_open_cover n hn i)
    (squareLocalData_bijective n i)

lemma actual_global_square_hom_inv (n : K) (hn : n≠0) (i : Fin 3) :
    (originalGlobalSquare n hn i).hom ≫ (originalGlobalSquare n hn i).inv=𝟙 _ :=
  (originalGlobalSquare n hn i).hom_inv_id
lemma actual_global_square_inv_hom (n : K) (hn : n≠0) (i : Fin 3) :
    (originalGlobalSquare n hn i).inv ≫ (originalGlobalSquare n hn i).hom=𝟙 _ :=
  (originalGlobalSquare n hn i).inv_hom_id

/-- Every ambient subopen retains the SAME old chart square coordinate.
The global trivialization has not discarded its normalization. -/
lemma actual_global_square_coordinate (n : K) (hn : n≠0) (i : Fin 3)
    (a : ULift.{u} (Option Bool)) (V : (originalCubicScheme n).Opens)
    (hV : V≤opens n i a) (s : Γ(squareModule n i,V)) :
    (originalGlobalSquare n hn i).hom.app V s=
      coordinate (embedding n i a.down) (squareModule n i) (chartSquare n i a.down).hom V hV s := by
  have hh := ModuleLocalGluing318.value_subopen (squareLocalData n i)
    (actual_open_cover n hn i) V V le_rfl a hV s
  rw [ModuleLocalGluing318.res_self,ModuleLocalGluing318.res_self] at hh
  exact hh
end ActualTwoDescentOriginalGlobalTensorSquare318
