module
public import ContactSchemePointRecovery318
public section
noncomputable section
namespace ContactSchemeHilbertEquiv318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (n : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
/-- The actual fixed-rank original quotient parameter classifies standard
full finite-flat finitely presented closed quotients on ALL coefficient
schemes, not just affine rings or geometric points. -/
@[expose] def equivalence : ContactSchemeHilbertData318.Data c n b ≃ ContactSchemePointFamily318.SchemePoint c n b where
  toFun := ContactSchemeHilbertLocalRecovery318.point c n b
  invFun := ContactSchemePointFamily318.extract c n b
  left_inv D := by apply ContactSchemeHilbertData318.Data.ext; exact ContactSchemeHilbertRecovery318.ideal_recovery c n b D
  right_inv := ContactSchemePointRecovery318.recover c n b
end ContactSchemeHilbertEquiv318
