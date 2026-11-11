module
public import RelativeLinePullbackComposition318
public import PELOriginalOrderFamilyCovariance318
public section
noncomputable section
namespace PELOriginalFppfOrderComposition318
open AlgebraicGeometry CategoryTheory PELPrincipalOrderCoordinates318
open PELOriginalProductChartCover318 PELOriginalOrderSchemeMorphism318
open PELOriginalFppfRosatiEquivariance318 PELOriginalOrderHermitianAdjoint318
variable (τ : ℂ) (hτ : 0 < τ.im)
/-- Genuine pullback composition on the WHOLE relative fppf line sheaf.
Categorical composition is kept explicit; no additive law on arbitrary
Picard classes is inferred from the group law on the original scheme. -/
lemma composition (a b : order) : action τ hτ (a*b)=action τ hτ a≫action τ hτ b := by
  have h := RelativeLinePullbackComposition318.fppf_comp (π τ hτ) (π τ hτ) (π τ hτ)
    (morphism τ hτ b) (over_complex τ hτ b)
    (morphism τ hτ a) (over_complex τ hτ a)
  rw [PELOriginalOrderSchemeLaws318.morphism_comp] at h
  exact h
/-- The literal order involution reverses the actual sheaf pullback
composition as dictated by the original noncommutative multiplication. -/
lemma adjoint_composition (a b : order) :
    action τ hτ (adjoint (a*b))=action τ hτ (adjoint b)≫action τ hτ (adjoint a) := by
  rw [PELOriginalOrderPositiveInvolution318.antimultiplicative,composition]
lemma adjoint_involutive (a : order) : action τ hτ (adjoint (adjoint a))=action τ hτ a := by
  rw [PELOriginalOrderPositiveInvolution318.involutive]
end PELOriginalFppfOrderComposition318
