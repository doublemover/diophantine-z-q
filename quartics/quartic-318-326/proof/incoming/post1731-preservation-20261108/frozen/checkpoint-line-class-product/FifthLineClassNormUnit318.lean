module
public import FifthLineClassNorm318
public import LineSheafUnit318
public import FifthNormUnit318
public section
noncomputable section
namespace FifthLineClassNormUnit318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open FifthCompletedGlobal318 FifthChartNorm318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- The actual sheaf-level norm-unit isomorphism gives the exact class value. -/
lemma norm_unit : FifthLineClassNorm318.norm (LineSheafUnit318.unitClass Model) =
    LineSheafUnit318.unitClass Target := by
  apply classOf_eq
  exact FifthNormUnit318.chosenIso _ (Iso.refl _)
    (LineSheafUnit318.line Model).opens (LineSheafUnit318.line Model).cover
    (LineSheafUnit318.line Model).frame
lemma norm_of_trivial (L : Line Model)
    (e : L.object ≅ SheafOfModules.unit Model.ringCatSheaf) :
    FifthLineClassNorm318.norm (classOf L) = LineSheafUnit318.unitClass Target := by
  apply classOf_eq
  exact FifthNormUnit318.chosenIso L.object e L.opens L.cover L.frame
end FifthLineClassNormUnit318
