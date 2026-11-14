module
public import ContactBoundedPointRecovery318
public section
noncomputable section
namespace ContactBoundedHilbertEquiv318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
/-- The actual bounded original Hilbert parameter classifies STANDARD
whole finite-flat/FP closed quotients of rank at most N on ALL coefficient
schemes. Neither constant rank nor a chosen rank decomposition is input. -/
@[expose] def equivalence : ContactBoundedSchemeHilbertData318.Data c N b ≃ ContactBoundedPointFamily318.SchemePoint c N b where
  toFun := ContactBoundedInputLocalRecovery318.point c N b
  invFun := ContactBoundedPointFamily318.extract c N b
  left_inv D := by apply ContactBoundedSchemeHilbertData318.Data.ext; exact ContactBoundedInputRecovery318.ideal_recovery c N b D
  right_inv := ContactBoundedPointRecovery318.recover c N b
end ContactBoundedHilbertEquiv318
