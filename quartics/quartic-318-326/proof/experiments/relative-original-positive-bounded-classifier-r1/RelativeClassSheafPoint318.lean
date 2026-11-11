module
public import FppfOpenCoverExt318
public import OriginalLineAbelTransformation318
public section
noncomputable section
namespace RelativeClassSheafPoint318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open RelativeLineClassBaseChange318 RelativeLineClassQuotient318
variable {C S B T : Scheme.{0}} (p : C ⟶ S) (b : B ⟶ S)

/-- The actual original line class pulled to a base test, before and
after the fixed canonical sheafification map. -/
@[expose] def original (L : Class C) : TestClass p b :=
  classMap (pullback.snd p b) (LineClassPullbackHom318.pullback (pullback.fst p b) L)
@[expose] def value (D : TestClass p b) := (RelativeFppfLineSheaf318.unit p).app (op (Over.mk b)) D

lemma original_test (j : T ⟶ B) (L : Class C) :
    testMap p b (j ≫ b) j rfl (original p b L)=original p (j ≫ b) L := by
  rw [original,testMap_class]
  change classMap (pullback.snd p (j ≫ b))
    (LineClassPullbackHom318.pullback (totalMap p b (j ≫ b) j rfl)
      (LineClassPullbackHom318.pullback (pullback.fst p b) L))=_
  rw [← MonoidHom.comp_apply,← LineClassPullbackHom318.composition,totalMap_fst]
  rfl

lemma value_restrict (t : T ⟶ S) (j : T ⟶ B) (hj : j ≫ b=t) (D : TestClass p b) :
    (RelativeFppfLineSheaf318.sheaf p).obj.map (Over.homMk j hj).op (value p b D)=
      value p t (testMap p b t j hj D) := by
  have h := congrArg (fun f => f D) ((RelativeFppfLineSheaf318.unit p).naturality
    (Over.homMk j hj).op)
  exact h.symm

/-- A family line identified with an ORIGINAL class on the full actual
coefficient cover has that class in the EXISTING associated fppf sheaf.
Local equalities alone are not incorrectly promoted to global absolute
line-class equality. -/
lemma original_of_cover (U : B.OpenCover) (D : TestClass p b) (L : Class C)
    (h : ∀ i,testMap p b (U.f i ≫ b) (U.f i) rfl D=original p (U.f i ≫ b) L) :
    value p b D=value p b (original p b L) := by
  apply FppfOpenCoverExt318.elements_ext b U (RelativeFppfLineSheaf318.sheaf p)
  intro i
  change (RelativeFppfLineSheaf318.sheaf p).obj.map
    (Over.homMk (U.f i) rfl).op (value p b D)=_
  rw [value_restrict,value_restrict,h i,original_test]
end RelativeClassSheafPoint318
