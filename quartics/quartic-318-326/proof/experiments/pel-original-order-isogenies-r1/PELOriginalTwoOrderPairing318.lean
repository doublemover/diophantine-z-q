module
public import PELOriginalOrderPositiveInvolution318
public section
noncomputable section
namespace PELOriginalTwoOrderPairing318
open AlgebraicGeometry CategoryTheory LineSheafClass318 PELPrincipalOrderCoordinates318
open PELOriginalSchemePointGroup318 PELOriginalPolarizationBicharacter318
open PELOriginalNormalizedPolarizationFamily318 PELOriginalOrderHermitianAdjoint318
variable (τ : ℂ) (hτ : 0 < τ.im) (a b : order)
variable {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ)) (x y : Points τ hτ T ρ)
abbrev act := PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ
lemma action_mul : act τ hτ ρ (a*b) y=act τ hτ ρ a (act τ hτ ρ b y) := by
  exact congrArg (fun f : AddMonoid.End (Points τ hτ T ρ) => f y)
    (map_mul (PELOriginalUniversalOrderAction318.ringAction τ hτ ρ) a b)
/-- Exact two-sided covariance in the original noncommutative order,
on all scheme tests, including nilpotents. The coefficient is a†b. -/
lemma covariance :
    pairing τ hτ ρ (act τ hτ ρ a x) (act τ hτ ρ b y)=
      pairing τ hτ ρ x (act τ hτ ρ (adjoint a*b) y) := by
  rw [PELOriginalRosatiTestPairing318.pairing_adjoint,action_mul]
/-- Moving both coefficients in the other direction gives b†a. -/
lemma covariance_left :
    pairing τ hτ ρ (act τ hτ ρ a x) (act τ hτ ρ b y)=
      pairing τ hτ ρ (act τ hτ ρ (adjoint b*a) x) y := by
  rw [symmetric τ hτ ρ (act τ hτ ρ a x) (act τ hτ ρ b y),
    covariance τ hτ b a ρ y x,symmetric]
@[expose] def iso :
    (normalizedLine τ hτ ρ (act τ hτ ρ a x) (act τ hτ ρ b y)).object ≅
      (normalizedLine τ hτ ρ x (act τ hτ ρ (adjoint a*b) y)).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [normalizedLine_class,normalizedLine_class,covariance]
end PELOriginalTwoOrderPairing318
