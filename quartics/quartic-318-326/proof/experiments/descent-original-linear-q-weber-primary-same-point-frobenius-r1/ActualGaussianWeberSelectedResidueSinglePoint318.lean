module
public import ActualGaussianWeberFaithfulArcPointTransfer318
public import ActualGaussianWeberActualPointFrob318
public section
noncomputable section

namespace ActualGaussianWeberSelectedResidueSinglePoint318

open NumberField IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberChosenPlaceLift318
open ActualGaussianWeberIntegerModel318 ActualGaussianWeberCanonicalRingFrob318
open ActualGaussianWeberActualLocalizedFrob318 ActualGaussianWeberActualPointFrob318
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberPlaceEquivariance318
open ActualGaussianWeberQuarterTurn318 ActualGaussianWeberGaussianScalarSpecialization318
open ActualGaussianWeberStockCoordinateHom318 ActualGaussianWeberOddNormGeneric318
open ActualGaussianWeberGaussLocalization318 ActualGaussianWeberTranslationFunctionField318
open ActualGaussianWeberFaithfulArcPointTransfer318

attribute [local instance] Classical.decEq

variable (L : Type*) [Field L] [NumberField L] [Algebra Base L] [DecidableEq L]
variable {p : ℕ} [Fact p.Prime]
variable (w : HeightOneSpectrum (𝓞 L)) [DecidableEq (ResidueField (AtPlace L w))]

private theorem scalar_eq_at_same_i {K : Type*} [Field K] [DecidableEq K] (hK : (2:K)≠0)
    {i i' : K} (hi : i^2= -1) (hi' : (i')^2= -1) (h : i=i')
    (a b : ℤ) (P : WP K) : gaussian hK i hi a b P=gaussian hK i' hi' a b P := by
  subst i'
  rfl

/-- Fill exactly one residue comparison for the same given original
point P and its actual signed prime w. No new prime is chosen and
there is no hypothesis concerning a different lift of P. In fact
torsion and primitivity are not needed for this residue-only step. -/
theorem selected_residual_comparison_for_same_point
    (a b : ℤ) (hN : a^2+b^2=(p:ℤ)) (h₂ : (2:ZMod p)≠0)
    (hUnder : SignedAt L w (rootOf (p:=p) a b) (rootOf_sq (p:=p) a b hN))
    (hGeneric :
      let h := function_two_ne (ZMod p) h₂
      let c := constGeneric (ZMod p) (rootOf (p:=p) a b)
      let hc : c^2= -1 := by
        simpa only [map_pow,map_neg,map_one] using
          congrArg (constGeneric (ZMod p)) (rootOf_sq (p:=p) a b hN)
      letI : CharP (FunctionField (ZMod p)) p := charP_along (constGeneric (ZMod p)) p
      gaussian h c hc a b (genericPoint (ZMod p) h₂)=
        coordinateHom (frobenius (FunctionField (ZMod p)) p) h (genericPoint (ZMod p) h₂))
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
  letI := integralAlgebra (algebraMap Base L)
  let V := AtPlace L w
  let K := ResidueField V
  let j := rootOf (p:=p) a b
  let hj := rootOf_sq (p:=p) a b hN
  let hR := residue_two_ne (L:=L) w j hj hUnder h₂
  let i := integralOverI (L:=L) w
  let hi := integralOverI_sq (L:=L) w
  let f : ZMod p→+*K := chosenEmbedding (L:=L) w j hj hUnder
  letI : CharP K p := actual_residue_char (L:=L) w j hj hUnder
  have hI : f j=residue V i := chosenEmbedding_i (L:=L) w j hj hUnder
  have hfI : (f j)^2= -1 := by
    simpa only [map_pow,map_neg,map_one] using congrArg f hj
  let Q := specialize V hR P
  have hOne : gaussian hR (f j) hfI a b Q=coordinateHom (frobenius K p) hR Q :=
    generic_identity_at_prescribed_point f h₂ hR j hj a b hGeneric Q
  have hF : residueArithmeticFrob L w j hj hUnder=frobenius K p := by
    apply RingHom.ext
    intro x
    change residueArithmeticFrob L w j hj hUnder x=x^p
    unfold residueArithmeticFrob <;> rfl
  change onCurvePoint (residueArithmeticFrob L w j hj hUnder) hR Q=
    gaussian hR (residue V i) (chosen_square_residue V i hi) a b Q
  calc
    _ = onCurvePoint (frobenius K p) hR Q :=
      congrArg (fun g : K→+*K => onCurvePoint g hR Q) hF
    _ = gaussian hR (f j) hfI a b Q := hOne.symm
    _ = _ := scalar_eq_at_same_i hR hfI (chosen_square_residue V i hi) hI a b Q

end ActualGaussianWeberSelectedResidueSinglePoint318
