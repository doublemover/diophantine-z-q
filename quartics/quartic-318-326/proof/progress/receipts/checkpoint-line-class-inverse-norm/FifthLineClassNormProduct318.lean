module
public import FifthLineClassNorm318
public import LineSheafTensor318
public import FifthNormChosenTensorIso318
public section
noncomputable section
namespace FifthLineClassNormProduct318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Multiplication is the actual tensor class, and the equality is induced by
the actual independently presented norm-tensor sheaf isomorphism. -/
lemma on_representatives (L N : Line Model) :
    FifthLineClassNorm318.norm (classOf (LineSheafTensor318.line L N)) =
      LineSheafTensor318.product (FifthLineClassNorm318.norm (classOf L))
        (FifthLineClassNorm318.norm (classOf N)) := by
  apply classOf_eq
  exact FifthNormChosenTensorIso318.iso L.object N.object L.opens N.opens
    (LineSheafTensor318.line L N).opens L.cover N.cover
    (LineSheafTensor318.line L N).cover L.frame N.frame
    (LineSheafTensor318.line L N).frame
lemma norm_product (c d : Class Model) :
    FifthLineClassNorm318.norm (LineSheafTensor318.product c d) =
      LineSheafTensor318.product (FifthLineClassNorm318.norm c) (FifthLineClassNorm318.norm d) :=
  Quotient.inductionOn₂ c d on_representatives
end FifthLineClassNormProduct318
