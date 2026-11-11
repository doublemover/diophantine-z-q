module
public import RelativeClassCoefficientComparison318
public section
noncomputable section
namespace RelativeClassCoefficientFunctor318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {C S R : Scheme.{u}} (p : C ⟶ S) (r : R ⟶ S)
/-- Exact comparison with the original naive presheaf restricted along
Over.map. Every component uses the original whole-family reassociation. -/
@[expose] def transformation : RelativeLineClassBaseChange318.presheaf (pullback.snd p r) ⟶
    (Over.map r).op ⋙ RelativeLineClassBaseChange318.presheaf p where
  app T := CommGrpCat.ofHom (RelativeClassCoefficientComparison318.toOriginal p r T.unop.hom)
  naturality T U f := CommGrpCat.hom_ext
    (RelativeClassCoefficientComparison318.natural p r T.unop.hom U.unop.hom f.unop.left f.unop.w)
end RelativeClassCoefficientFunctor318
