module
public import LineSheafInverse318
public import LineSheafClass318
public section
noncomputable section
namespace FramedLineInverse318
open AlgebraicGeometry CategoryTheory IntrinsicTensorSheaf318
universe u
variable {X:Scheme.{u}}
/-- The actual inverse framed line, retaining the original covering opens. -/
@[expose] def inverse (L:LineSheafClass318.Line X):LineSheafClass318.Line X where
  object:=LineSheafInverse318.object L.object L.opens L.frame
  Index:=L.Index
  opens:=L.opens
  cover:=L.cover
  frame:=LineSheafInverse318.frame L.object L.opens L.frame
@[expose] def rightIso (L:LineSheafClass318.Line X):
    tensor L.object (inverse L).object≅SheafOfModules.unit X.ringCatSheaf:=
  LineSheafInverse318.rightIso L.object L.opens L.frame L.cover
@[expose] def leftIso (L:LineSheafClass318.Line X):
    tensor (inverse L).object L.object≅SheafOfModules.unit X.ringCatSheaf:=
  LineSheafInverse318.leftIso L.object L.opens L.frame L.cover
lemma right_hom_inv (L:LineSheafClass318.Line X):
    (rightIso L).hom≫(rightIso L).inv=𝟙 _ :=(rightIso L).hom_inv_id
lemma right_inv_hom (L:LineSheafClass318.Line X):
    (rightIso L).inv≫(rightIso L).hom=𝟙 _ :=(rightIso L).inv_hom_id
lemma left_hom_inv (L:LineSheafClass318.Line X):
    (leftIso L).hom≫(leftIso L).inv=𝟙 _ :=(leftIso L).hom_inv_id
lemma left_inv_hom (L:LineSheafClass318.Line X):
    (leftIso L).inv≫(leftIso L).hom=𝟙 _ :=(leftIso L).inv_hom_id
end FramedLineInverse318
