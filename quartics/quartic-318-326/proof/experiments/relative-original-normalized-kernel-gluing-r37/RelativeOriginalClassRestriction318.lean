module
public import RelativePairParameter318
public section
noncomputable section
namespace RelativeOriginalClassRestriction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open RelativeLineClassBaseChange318 RelativeClassSheafPoint318
variable {C S B T : Scheme.{0}} (p : C ⟶ S) (b : B ⟶ S) (t : T ⟶ S)
  (j : T ⟶ B) (hj : j ≫ b=t) (L : Class C)
/-- The original class follows an arbitrary literal commuting base
map, without changing the chosen target base by a definitional abbreviation. -/
lemma original : testMap p b t j hj (RelativeClassSheafPoint318.original p b L)=
    RelativeClassSheafPoint318.original p t L := by
  rw [RelativeClassSheafPoint318.original,RelativeLineClassBaseChange318.testMap_class]
  change RelativeLineClassQuotient318.classMap (pullback.snd p t)
    (LineClassPullbackHom318.pullback (totalMap p b t j hj)
      (LineClassPullbackHom318.pullback (pullback.fst p b) L))=_
  rw [←MonoidHom.comp_apply,←LineClassPullbackHom318.composition,totalMap_fst]
  rfl
lemma value_original : (RelativeFppfLineSheaf318.sheaf p).obj.map (Over.homMk j hj).op
    (value p b (RelativeClassSheafPoint318.original p b L))=
      value p t (RelativeClassSheafPoint318.original p t L) := by
  rw [value_restrict,original]
/-- Genuine sheaf equality on a whole parameter restricts to the actual
common parameter; no equality of absolute line classes is inferred. -/
lemma restrict_equal (a : TestClass p b)
    (h : value p b a=value p b (RelativeClassSheafPoint318.original p b L)) :
    value p t (testMap p b t j hj a)=value p t (RelativeClassSheafPoint318.original p t L) := by
  have he := congrArg (fun x => (RelativeFppfLineSheaf318.sheaf p).obj.map (Over.homMk j hj).op x) h
  simpa only [value_restrict,original] using he
end RelativeOriginalClassRestriction318
