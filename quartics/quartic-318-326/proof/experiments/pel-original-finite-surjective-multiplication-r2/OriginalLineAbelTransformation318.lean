module
public import RelativeFppfLineSheaf318
public import LineSheafClass318
public section
noncomputable section
namespace OriginalLineAbelTransformation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open RelativeLineClassBaseChange318 RelativeLineClassQuotient318
universe u
variable {C S B : Scheme.{u}} (p : C ⟶ S) (b : B ⟶ S)
  (L : Line (pullback p b))

/-- The original relative class of the actual family line, on the
actual fiber product over the specified parameter scheme. -/
@[expose] def point : TestClass p b :=
  classMap (pullback.snd p b) (classOf L)

/-- The genuine natural transformation on ALL scheme tests over the
base, taking a parameter map to the original pulled relative line class.
No geometric-point surrogate or target representability is assumed. -/
@[expose] def naive : yoneda.obj (Over.mk b) ⟶
    presheaf p ⋙ forget CommGrpCat.{u+1} where
  app T a := testMap p b T.unop.hom a.left a.w (point p b L)
  naturality T T' a := by
    funext h
    exact congrArg (fun k => k (point p b L))
      (testMap_composition p b T.unop.hom T'.unop.hom h.left a.unop.left h.w a.unop.w _)

/-- An actual Abel-type map into the EXISTING associated fppf line-class
sheaf, via its canonical sheafification unit. This does not turn that
sheaf into a representing scheme or identify its degree-zero component. -/
@[expose] def transformation : yoneda.obj (Over.mk b) ⟶
    (RelativeFppfLineSheaf318.sheaf p).obj ⋙ forget CommGrpCat.{u+1} :=
  naive p b L ≫ Functor.whiskerRight (RelativeFppfLineSheaf318.unit p) (forget CommGrpCat.{u+1})

lemma apply (T : Over S) (a : T ⟶ Over.mk b) :
    (transformation p b L).app (op T) a=
      (RelativeFppfLineSheaf318.unit p).app (op T)
        (testMap p b T.hom a.left a.w (point p b L)) := rfl

/-- Equal original global line classes give the same actual natural
transformation, not merely the same values on field-valued points. -/
lemma class_congr (N : Line (pullback p b)) (h : classOf L=classOf N) :
    transformation p b L=transformation p b N := by
  have hp : point p b L=point p b N := congrArg (classMap (pullback.snd p b)) h
  ext T a
  change (RelativeFppfLineSheaf318.unit p).app T
    (testMap p b T.unop.hom a.left a.w (point p b L))=
    (RelativeFppfLineSheaf318.unit p).app T
      (testMap p b T.unop.hom a.left a.w (point p b N))
  rw [hp]
end OriginalLineAbelTransformation318
