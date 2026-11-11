module
public import RelativeClassCoefficientFunctor318
public import Mathlib.CategoryTheory.Sites.Over
public section
noncomputable section
namespace RelativeFppfCoefficientRestriction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {C S R : Scheme.{u}} (p : C ⟶ S) (r : R ⟶ S)
/-- Restriction of the ACTUAL original fppf group sheaf to the actual
coefficient slice. Continuity of Over.map is supplied by the native big
site theorem; no sheaf property is inserted as an assumption. -/
@[expose] def target : Sheaf (RelativeFppfLineSheaf318.topology R) CommGrpCat.{u+1} :=
  (Scheme.fppfTopology.overMapPullback CommGrpCat.{u+1} r).obj (RelativeFppfLineSheaf318.sheaf p)
@[expose] def naive : RelativeLineClassBaseChange318.presheaf (pullback.snd p r) ⟶ (target p r).obj :=
  RelativeClassCoefficientFunctor318.transformation p r ≫
    Functor.whiskerLeft (Over.map r).op (RelativeFppfLineSheaf318.unit p)
/-- The genuine associated-sheaf map induced by that exact naive
comparison. It transports proven relative equalities to the original
base sheaf without assuming that sheafification is injective. -/
@[expose] def comparison : RelativeFppfLineSheaf318.sheaf (pullback.snd p r) ⟶ target p r :=
  RelativeFppfLineSheaf318.lift (pullback.snd p r) (target p r) (naive p r)
lemma unit_comparison : RelativeFppfLineSheaf318.unit (pullback.snd p r) ≫ (comparison p r).hom=naive p r :=
  RelativeFppfLineSheaf318.unit_lift (pullback.snd p r) (target p r) (naive p r)
lemma on_unit {B : Scheme.{u}} (b : B ⟶ R) (x : RelativeLineClassBaseChange318.TestClass (pullback.snd p r) b) :
    (comparison p r).hom.app (Opposite.op (Over.mk b))
      ((RelativeFppfLineSheaf318.unit (pullback.snd p r)).app (Opposite.op (Over.mk b)) x)=
      (RelativeFppfLineSheaf318.unit p).app (Opposite.op (Over.mk (b ≫ r)))
        (RelativeClassCoefficientComparison318.toOriginal p r b x) := by
  have h := congrArg (fun η => η.app (Opposite.op (Over.mk b))) (unit_comparison p r)
  exact ConcreteCategory.congr_hom h x
end RelativeFppfCoefficientRestriction318
