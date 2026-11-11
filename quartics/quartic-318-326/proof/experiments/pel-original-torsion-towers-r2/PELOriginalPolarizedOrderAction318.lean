module
public import PELOriginalFppfOrderComposition318
public section
noncomputable section
namespace PELOriginalPolarizedOrderAction318
open AlgebraicGeometry CategoryTheory PELPrincipalOrderCoordinates318
open PELOriginalOrderHermitianAdjoint318 PELOriginalOrderSchemeMorphism318
open PELOriginalSchemePointGroup318 PELOriginalProductChartCover318
variable (τ : ℂ) (hτ : 0 < τ.im)
/-- The original order remains faithful as actual algebraic group
endomorphisms, with the same positive involution used by the actual
normalized-family comparison. -/
lemma faithful : Function.Injective (morphism τ hτ) :=
  PELOriginalOrderActionFaithful318.scheme_action_injective τ hτ
lemma involution (a : order) : morphism τ hτ (adjoint (adjoint a))=morphism τ hτ a := by
  rw [PELOriginalOrderPositiveInvolution318.involutive]
lemma composition_adjoint (a b : order) :
    morphism τ hτ (adjoint (a*b))=
      morphism τ hτ (adjoint a)≫morphism τ hτ (adjoint b) := by
  rw [PELOriginalOrderPositiveInvolution318.antimultiplicative,
    PELOriginalOrderSchemeLaws318.morphism_comp]
lemma central_integer (n : ℤ) :
    morphism τ hτ (adjoint (n : order))=PELOriginalIntegerMultiplication318.multiplication τ hτ n := by
  rw [PELOriginalOrderPositiveInvolution318.integer,
    PELOriginalOrderIntegerCompatibility318.integer_morphism]
/-- Simultaneous faithful action, positivity and exact all-test adjoint
covariance for the SAME original line. This is a concrete PEL action
interface; neither dual representability nor a Jacobian is asserted. -/
theorem actual_polarized_action :
    Function.Injective (morphism τ hτ) ∧
    (∀ a : order,a≠0 → 0<PELQuaternionAlgebra318.reducedTrace
      ((a:PELQuaternionAlgebra318.B)*(adjoint a:PELQuaternionAlgebra318.B))) ∧
    (∀ (T : Scheme) (ρ : T⟶Spec (CommRingCat.of ℂ)) (a b : order)
      (x y : Points τ hτ T ρ),
      PELOriginalPolarizationBicharacter318.pairing τ hτ ρ
        (PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ a x)
        (PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ b y)=
      PELOriginalPolarizationBicharacter318.pairing τ hτ ρ x
        (PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ (adjoint a*b) y)) :=
  ⟨faithful τ hτ,PELOriginalOrderPositiveInvolution318.positive,
    fun _ ρ a b x y => PELOriginalTwoOrderPairing318.covariance τ hτ a b ρ x y⟩
end PELOriginalPolarizedOrderAction318
