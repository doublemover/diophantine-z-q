module
public import PELOriginalRelativeRosatiAction318
public import PELOriginalRelativePolarizationGroupTransformation318
public section
noncomputable section
namespace PELOriginalFppfRosatiEquivariance318
open AlgebraicGeometry CategoryTheory Opposite PELPrincipalOrderCoordinates318
open PELOriginalProductChartCover318 PELOriginalSchemePointGroup318
open PELOriginalRelativePolarizationTransformation318 PELOriginalOrderHermitianAdjoint318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order)
/-- Actual pullback by the original algebraic order action on the actual
associated fppf line sheaf. No representing dual scheme is required. -/
@[expose] def action : Target τ hτ ⟶ Target τ hτ :=
  RelativeFppfLineSheaf318.pullback (π τ hτ) (π τ hτ)
    (PELOriginalOrderSchemeMorphism318.morphism τ hτ a)
    (PELOriginalOrderSchemeMorphism318.over_complex τ hτ a)
lemma action_unit (T : Over (Spec (CommRingCat.of ℂ)))
    (c : RelativeLineClassBaseChange318.TestClass (π τ hτ) T.hom) :
    (action τ hτ a).hom.app (op T)
      ((RelativeFppfLineSheaf318.unit (π τ hτ)).app (op T) c)=
    (RelativeFppfLineSheaf318.unit (π τ hτ)).app (op T)
      (PELOriginalRelativeRosatiAction318.action τ hτ a T.hom c) := by
  have he := congrArg (fun f => (f.app (op T)) c)
    (RelativeFppfLineSheaf318.unit_pullback (π τ hτ) (π τ hτ)
      (PELOriginalOrderSchemeMorphism318.morphism τ hτ a)
      (PELOriginalOrderSchemeMorphism318.over_complex τ hτ a))
  exact he.symm
/-- Full all-test compatibility of the unchanged original polarization
transformation with actual pullback by the literal Rosati adjoint. -/
lemma equivariance (T : Over (Spec (CommRingCat.of ℂ)))
    (x : Points τ hτ T.left T.hom) :
    (action τ hτ a).hom.app (op T)
      ((transformation τ hτ).app (op T) (Over.homMk x.val x.property))=
    (transformation τ hτ).app (op T)
      (Over.homMk
        (PELOriginalUniversalOrderAction318.endomorphism τ hτ T.hom (adjoint a) x).val
        (PELOriginalUniversalOrderAction318.endomorphism τ hτ T.hom (adjoint a) x).property) := by
  rw [←PELOriginalRelativePolarizationGroupTransformation318.hom_eq_transformation,
    ←PELOriginalRelativePolarizationGroupTransformation318.hom_eq_transformation]
  change (action τ hτ a).hom.app (op T)
      ((RelativeFppfLineSheaf318.unit (π τ hτ)).app (op T)
        (PELOriginalRelativePolarizationHom318.relativeValue τ hτ T.hom x))=
    (RelativeFppfLineSheaf318.unit (π τ hτ)).app (op T)
      (PELOriginalRelativePolarizationHom318.relativeValue τ hτ T.hom
        (PELOriginalUniversalOrderAction318.endomorphism τ hτ T.hom (adjoint a) x))
  rw [action_unit,PELOriginalRelativeRosatiAction318.polarization_equivariance]
/-- Equality of actual natural transformations, not merely their complex
points. Sheafification retains the proved relative quotient equation. -/
lemma transformation_equivariance :
    transformation τ hτ ≫ whiskerRight (action τ hτ a).hom (forget CommGrpCat.{1})=
      yoneda.map (Over.homMk (PELOriginalOrderSchemeMorphism318.morphism τ hτ (adjoint a))
        (PELOriginalOrderSchemeMorphism318.over_complex τ hτ (adjoint a))) ≫
      transformation τ hτ := by
  ext T x
  exact equivariance τ hτ a T.unop ⟨x.left,x.w⟩
end PELOriginalFppfRosatiEquivariance318
