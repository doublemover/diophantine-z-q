module
public import LineSheafClass318
public import StructureLineFrames318
public section
noncomputable section
namespace LineSheafUnit318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
/-- The original structure-module sheaf with its genuine whole-open frame. -/
@[expose] def line (X : Scheme.{u}) : Line X where
  object := SheafOfModules.unit X.ringCatSheaf
  Index := PUnit
  opens := fun _ => ⊤
  cover := by simp
  frame := fun _ => StructureLineFrames318.frame X ⊤
@[expose] def unitClass (X : Scheme.{u}) : Class X := classOf (line X)
lemma eq_unitClass_iff {X : Scheme.{u}} (L : Line X) :
    classOf L = unitClass X ↔ Nonempty (L.object ≅ SheafOfModules.unit X.ringCatSheaf) :=
  classOf_eq_iff L (line X)
end LineSheafUnit318
