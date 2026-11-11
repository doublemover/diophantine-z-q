module
public import LineArrowInverseLocal318
public import ModuleGlobalSections318
public section
noncomputable section
namespace LineArrowInverseSection318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open ModuleLocalGluing318 LineArrowInverseLocal318
universe u
variable {X : Scheme.{u}} (L : Line X) (f : L.object ⟶ SheafOfModules.unit X.ringCatSheaf)
local notation "I" => FramedLineInverse318.inverse L

/-- Original inclusion coefficients glue as an actual global map into
its inverse line, with the original transition units and scalar maps. -/
@[expose] def data : LocalData (SheafOfModules.unit X.ringCatSheaf) I.object L.opens where
  map := localMap L f
  natural := natural L f
  compatible := compatible L f
@[expose] def hom : SheafOfModules.unit X.ringCatSheaf ⟶ I.object :=
  ModuleLocalGluing318.hom (data L f) L.cover

lemma hom_on_subopen (i : L.Index) (V : X.Opens) (hV : V≤L.opens i) (a : Γ(X,V)) :
    (hom L f).app V a=localMap L f i V hV a := by
  have h := ModuleLocalGluing318.value_subopen (data L f) L.cover V V le_rfl i hV a
  simpa only [res_self] using h

@[expose] def section : Γ(I.object,⊤) := (hom L f).app ⊤ 1

/-- The canonical inverse-line section has exactly the original
inclusion coefficient in every inverse frame, over every subopen. -/
lemma section_coordinate (i : L.Index) (V : X.Opens) (hV : V≤L.opens i) :
    (inverseFrame L i V hV).symm (res I.object (show V≤⊤ from le_top) (section L f))=
      coefficient L f i V hV := by
  have hn := congrArg (fun k => k (1 : Γ(X,⊤)))
    ((hom L f).val.naturality (homOfLE (show V≤⊤ from le_top)).op)
  change (inverseFrame L i V hV).symm
    (I.object.presheaf.map (homOfLE (show V≤⊤ from le_top)).op ((hom L f).app ⊤ 1))=_
  rw [← hn,map_one,hom_on_subopen]
  change (inverseFrame L i V hV).symm
    (inverseFrame L i V hV (1*coefficient L f i V hV))=_
  rw [LinearEquiv.symm_apply_apply,one_mul]
end LineArrowInverseSection318
