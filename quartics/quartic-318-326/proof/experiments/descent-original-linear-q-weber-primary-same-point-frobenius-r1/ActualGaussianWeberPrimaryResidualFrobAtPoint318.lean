module
public import ActualGaussianWeberSelectedBaseGenericFrob318
public import ActualGaussianWeberSelectedResidueSinglePoint318
public section
noncomputable section

namespace ActualGaussianWeberPrimaryResidualFrobAtPoint318

open NumberField IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberChosenPlaceLift318
open ActualGaussianWeberIntegerModel318 ActualGaussianWeberCanonicalRingFrob318
open ActualGaussianWeberActualPointFrob318 ActualGaussianWeberHenselianPointMap318
open ActualGaussianWeberPlaceEquivariance318 ActualGaussianWeberQuarterTurn318
open ActualGaussianWeberGaussianScalarSpecialization318
open ActualGaussianWeberSelectedBaseGenericFrob318 ActualGaussianWeberSelectedResidueSinglePoint318

attribute [local instance] Classical.decEq

variable (L : Type*) [Field L] [NumberField L] [Algebra Base L] [DecidableEq L]
variable {p : ℕ} [Fact p.Prime]
variable (w : HeightOneSpectrum (𝓞 L)) [DecidableEq (ResidueField (AtPlace L w))]

/-- The selected primary Gaussian scalar equals the actual arithmetic
residue Frobenius at the reduction of this same named point. The point
can be the previously specified primitive point; it is not rechosen.
The generic identity is supplied by the verified selected-base assembly. -/
theorem selected_residual_frob_of_primary
    (hOdd : Odd (p : ℤ)) (h₂ : (2 : ZMod p) ≠ 0)
    (a b c d : ℤ) (hN : a^2+b^2=(p:ℤ))
    (ha : a=1-2*(c+d)) (hb : b=2*(c-d))
    (hUnder : SignedAt L w (rootOf (p:=p) a b) (rootOf_sq (p:=p) a b hN))
    (P : WP L) :
    letI := integralAlgebra (algebraMap Base L)
    let V := AtPlace L w
    let j := rootOf (p:=p) a b
    let hj := rootOf_sq (p:=p) a b hN
    let hR := residue_two_ne (L:=L) w j hj hUnder h₂
    let i := integralOverI (L:=L) w
    let hi := integralOverI_sq (L:=L) w
    onCurvePoint (residueArithmeticFrob L w j hj hUnder) hR (specialize V hR P)=
      gaussian hR (residue V i) (chosen_square_residue V i hi) a b (specialize V hR P) := by
  exact selected_residual_comparison_for_same_point (p:=p) L w a b hN h₂ hUnder
    (primary_generic_primefield_frobenius (p:=p) hOdd h₂ a b c d hN ha hb) P

end ActualGaussianWeberPrimaryResidualFrobAtPoint318
