module
public import RelativeClassCoefficientValues318
public section
noncomputable section
namespace RelativeFppfCoefficientEquality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open RelativeClassSheafPoint318
variable {C S R B : Scheme.{0}} (p : C ⟶ S) (r : R ⟶ S) (b : B ⟶ R)
local notation "q" => pullback.snd p r
local notation "e" => RelativeAmbientReassociation318.comparison p r b
/-- A relative equality proved over the coefficient-changed curve
implies the intended equality in the ORIGINAL base fppf sheaf. This
uses its genuine associated-sheaf comparison, not injectivity of the
sheafification unit or an identification assumed between two sheaves. -/
lemma transport (K : Line (pullback p (b ≫ r))) (L : Class (pullback p r))
    (h : value q b (OriginalLineAbelTransformation318.point q b (LineSheafPullback318.line e.hom K))=
      value q b (original q b L)) :
    value p (b ≫ r) (OriginalLineAbelTransformation318.point p (b ≫ r) K)=
      (RelativeFppfLineSheaf318.sheaf p).obj.map (Over.homMk b rfl).op
        (value p r (RelativeLineClassQuotient318.classMap (pullback.snd p r) L)) := by
  have he := congrArg ((RelativeFppfCoefficientRestriction318.comparison p r).hom.app
    (op (Over.mk b))) h
  change (RelativeFppfCoefficientRestriction318.comparison p r).hom.app (op (Over.mk b))
      ((RelativeFppfLineSheaf318.unit q).app (op (Over.mk b)) _)=
    (RelativeFppfCoefficientRestriction318.comparison p r).hom.app (op (Over.mk b))
      ((RelativeFppfLineSheaf318.unit q).app (op (Over.mk b)) _) at he
  rw [RelativeFppfCoefficientRestriction318.on_unit,RelativeFppfCoefficientRestriction318.on_unit] at he
  change (RelativeFppfLineSheaf318.unit p).app (op (Over.mk (b ≫ r)))
    (RelativeClassCoefficientComparison318.toOriginal p r b
      (RelativeLineClassQuotient318.classMap (pullback.snd q b)
        (LineClassPullbackHom318.pullback e.hom (classOf K))))=
    (RelativeFppfLineSheaf318.unit p).app (op (Over.mk (b ≫ r)))
      (RelativeClassCoefficientComparison318.toOriginal p r b
        (RelativeLineClassQuotient318.classMap (pullback.snd q b)
          (LineClassPullbackHom318.pullback (pullback.fst q b) L))) at he
  rw [RelativeClassCoefficientValues318.pulled,RelativeClassCoefficientValues318.original] at he
  rw [RelativeClassSheafPoint318.value_restrict]
  exact he
end RelativeFppfCoefficientEquality318
