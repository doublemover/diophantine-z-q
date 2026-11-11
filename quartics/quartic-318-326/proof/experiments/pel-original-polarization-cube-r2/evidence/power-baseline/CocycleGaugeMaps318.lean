module
public import CocycleModule318
public import OpenClutchedGauge318
public section
noncomputable section
namespace CocycleGaugeMaps318
open AlgebraicGeometry CategoryTheory Opposite
open ClutchedGaugeMultiplication318
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    (c d:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
    (a:∀i,Γ(X,U i)ˣ)
    (h:∀i j,d.transition i j=UnitTransitionCocycle318.coboundary
      (StructureUnitsSheaf318.units X).obj U a i j*c.transition i j)
@[expose] def scale (i:ι):CocycleModule318.chart U i⟶CocycleModule318.chart U i:=
  (Scheme.Modules.pushforward (U i).ι).map
    (ClutchedModule318.multiply ((U i).topIso.inv (a i).val))
@[expose] def overlapScale (i j:ι):CocycleModule318.overlap U i j⟶CocycleModule318.overlap U i j:=
  (Scheme.Modules.pushforward (OpenClutchedLine318.leftInclusion (U i) (U j)≫(U i).ι)).map
    (ClutchedModule318.multiply ((OpenClutchedLine318.leftInclusion (U i) (U j)).appTop
      ((U i).topIso.inv (a i).val)))
lemma left_square (i j:ι):scale U a i≫CocycleModule318.left U i j=
    CocycleModule318.left U i j≫overlapScale U a i j:=
  restriction_multiply (U i).ι (OpenClutchedLine318.leftInclusion (U i) (U j)) _
include h in
lemma scalar_square (i j:ι):
    X.presheaf.map (homOfLE (show U i⊓U j≤U j from inf_le_right)).op (a j).val*(d.transition i j).val=
      (c.transition i j).val*X.presheaf.map (homOfLE (show U i⊓U j≤U i from inf_le_left)).op (a i).val:=by
  have hu:UnitTransitionCocycle318.restrict (StructureUnitsSheaf318.units X).obj inf_le_right (a j)*d.transition i j=
      c.transition i j*UnitTransitionCocycle318.restrict (StructureUnitsSheaf318.units X).obj inf_le_left (a i):=by
    rw [h,UnitTransitionCocycle318.coboundary]
    simp only [mul_assoc,mul_left_comm,mul_comm,inv_mul_cancel_left,mul_inv_cancel,mul_one,one_mul]
  exact congrArg Units.val hu
include h in
lemma right_square (i j:ι):scale U a j≫CocycleModule318.right U d i j=
    CocycleModule318.right U c i j≫overlapScale U a i j:=
  second_square (U i).ι (U j).ι
    (OpenClutchedLine318.leftInclusion (U i) (U j))
    (OpenClutchedLine318.rightInclusion (U i) (U j))
    (OpenClutchedLine318.square (U i) (U j)) _ _ _ _
    (OpenClutchedGauge318.compatible (U i) (U j) (c.transition i j) (d.transition i j)
      (a i) (a j) (scalar_square U c d a h i j))
include h in
lemma compatible (i j:ι):
    (CocycleModule318.coefficient U c i≫scale U a i)≫CocycleModule318.left U i j=
      (CocycleModule318.coefficient U c j≫scale U a j)≫CocycleModule318.right U d i j:=by
  rw [Category.assoc,left_square,←Category.assoc,CocycleModule318.compatible,
    Category.assoc,←right_square U c d a h,←Category.assoc]
/-- Actual map with the supplied change of original coefficient units. -/
@[expose] def map:CocycleModule318.object U c⟶CocycleModule318.object U d:=
  CocycleModule318.lift U d (fun i=>CocycleModule318.coefficient U c i≫scale U a i)
    (compatible U c d a h)
lemma map_coefficient (i:ι):map U c d a h≫CocycleModule318.coefficient U d i=
    CocycleModule318.coefficient U c i≫scale U a i:=
  CocycleModule318.lift_coefficient _ _ _ _ i
end CocycleGaugeMaps318
