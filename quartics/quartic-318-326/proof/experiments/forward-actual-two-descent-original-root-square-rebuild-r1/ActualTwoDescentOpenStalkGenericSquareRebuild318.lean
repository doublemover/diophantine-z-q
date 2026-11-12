module
public import ActualTwoDescentOriginalAllStalkFractionsRebuild318
public section
noncomputable section
namespace ActualTwoDescentOpenStalkGenericSquareRebuild318
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (j : X ⟶ Y) [IsOpenImmersion j]

/-- The actual generic comparison commutes with the specialization map
from EVERY source stalk. Native point transport is retained. -/
lemma square (p : X) :
    Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ (j p))) ≫
        (OpenFunctionField318.fieldIso j).hom =
      j.stalkMap p ≫
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ p)) := by
  dsimp only [OpenFunctionField318.fieldIso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  rw [← Category.assoc, TopCat.Presheaf.stalkCongr_inv,
    TopCat.Presheaf.stalkSpecializes_comp]
  exact j.stalkSpecializes_stalkMap (genericPoint X) p
    ((genericPoint_spec X).specializes (Set.mem_univ p))

lemma square_apply (p : X) (s : Y.presheaf.stalk (j p)) :
    OpenFunctionField318.fieldEquiv j
      (algebraMap (Y.presheaf.stalk (j p)) Y.functionField s) =
        algebraMap (X.presheaf.stalk p) X.functionField (j.stalkMap p s) := by
  exact congrArg (fun f => f s) (square j p)
end ActualTwoDescentOpenStalkGenericSquareRebuild318
