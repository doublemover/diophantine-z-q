module
public import ActualGaussianWeberChosenResidualDescriptor318
public import ActualGaussianWeberSelectedSameRatioDerivative318
public import ActualGaussianWeberActualOriginPurePowers318
public import ActualGaussianWeberPrimaryOneAffineProbe318
public import Mathlib.FieldTheory.Finite.Basic
public import ActualGaussianWeberSelectedPrimeFieldFrobTransport318
public section
noncomputable section

namespace ActualGaussianWeberSelectedBaseGenericFrob318

open IsLocalRing Polynomial WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberSelectedGaussianPrime318
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberPlaceEquivariance318
open ActualGaussianWeberGaussLocalization318 ActualGaussianWeberGenericChartDomain318
open ActualGaussianWeberQuadraticGenericChart318 ActualGaussianWeberTranslationFunctionField318
open ActualGaussianWeberOddNormGeneric318 ActualGaussianWeberQuarterTurn318
open ActualGaussianWeberGaussianScalarSpecialization318 ActualGaussianWeberStockCoordinateHom318
open ActualGaussianWeberChosenResidualDescriptor318 ActualGaussianWeberSelectedSameRatioDerivative318
open ActualGaussianWeberActualOriginPurePowers318 ActualGaussianWeberPrimaryOneAffineProbe318

attribute [local instance] Classical.decEq

open ActualGaussianWeberSelectedPrimeFieldFrobTransport318

/-- No point, rational presentation, cap, derivative or phase is
supplied as an extra generic input. The single finite descriptor
fixes the same coordinates, normalized ratio and selected place
for all four gates. The primary congruence is an arithmetic input. -/
theorem positive_selected_base_coordinates {p : ℕ} [Fact p.Prime]
    (hOdd : Odd (p : ℤ)) (a b c d : ℤ) (hN : a^2+b^2=(p:ℤ))
    (ha : a=1-2*(c+d)) (hb : b=2*(c-d)) :
    let s := rootOf (p:=p) a b
    let hs := rootOf_sq (p:=p) a b hN
    let V := BasePlace s hs
    let k := ResidueField V
    let i := integralI s hs
    let j := residue V i
    let h₂ := residue_two_ne_at_odd_selected_prime hOdd s hs
    ∃ u v : FunctionField k, ∃ huv : (curve (FunctionField k)).toAffine.Nonsingular u v,
      gaussian (function_two_ne k h₂) (constGeneric k j)
        (by simpa only [map_pow,map_neg,map_one] using
          congrArg (constGeneric k) (chosen_square_residue V i (integralI_sq s hs)))
        a b (genericPoint k h₂)=Point.some u v huv ∧
      u=(xGeneric k)^p ∧ v=(yGeneric k)^p := by
  let s := rootOf (p:=p) a b
  let hs := rootOf_sq (p:=p) a b hN
  let V := BasePlace s hs
  let k := ResidueField V
  let i := integralI s hs
  let j := residue V i
  let h₂ := residue_two_ne_at_odd_selected_prime hOdd s hs
  let e := residueEquiv s hs
  letI : CharP k p := field_characteristic_along e.symm.toRingHom p
  have hj := chosen_square_residue V i (integralI_sq s hs)
  have hjFixed : j^p=j := by
    apply e.injective
    exact (map_pow e j p).trans (ZMod.pow_card (e j))
  obtain ⟨_,_,_,_,r,_,_,u,v,huv,hGen,D,_,_,_,_,_,hCap,hRat⟩ :=
    actual_selected_descriptor (p := p) hOdd a b hN
  let R := RatFunc.mk (D.num.map (residue V)) (D.den.map (residue V))
  have hDerivative : R.num.derivative * R.denom - R.num * R.denom.derivative = 0 :=
    actual_selected_cross_of_descriptor (p := p) a b hN h₂ R u v huv hGen hRat
  have hShape := actual_scalar_pure_power_shapes (p := p) h₂ j hj a b hN hOdd
    R u v huv hGen hRat hCap hDerivative
  obtain ⟨hu,hv⟩ := positive_powers_from_same_named_probe (p := p) h₂ j hj hjFixed a b c d ha hb
    u v huv hGen hShape
  exact ⟨u,v,huv,hGen,hu,hv⟩

/-- Transport through the actual signed residue equivalence to the
interface needed by prime-selection: the generic point over ZMod p.
The Frobenius here is precisely the stock p-power point map, not an
arithmetic Galois lift or an assertion about all geometric points. -/
theorem primary_generic_primefield_frobenius {p : ℕ} [Fact p.Prime]
    (hOdd : Odd (p:ℤ)) (h₂ : (2:ZMod p) ≠ 0)
    (a b c d : ℤ) (hN : a^2+b^2=(p:ℤ))
    (ha : a=1-2*(c+d)) (hb : b=2*(c-d)) :
    let k₁ := ZMod p
    let h₁ := function_two_ne k₁ h₂
    let j₁ := constGeneric k₁ (rootOf (p:=p) a b)
    let hj₁ : j₁^2= -1 := by
      simpa only [map_pow,map_neg,map_one] using
        congrArg (constGeneric k₁) (rootOf_sq (p:=p) a b hN)
    letI : CharP (FunctionField k₁) p := field_characteristic_along (constGeneric k₁) p
    gaussian h₁ j₁ hj₁ a b (genericPoint k₁ h₂)=
      coordinateHom (frobenius (FunctionField k₁) p) h₁ (genericPoint k₁ h₂) := by
  let s := rootOf (p:=p) a b
  let hs := rootOf_sq (p:=p) a b hN
  let h₀ := residue_two_ne_at_odd_selected_prime hOdd s hs
  obtain ⟨u,v,huv,hGen,hu,hv⟩ := positive_selected_base_coordinates hOdd a b c d hN ha hb
  exact primefield_frobenius_of_base_powers (p := p) s hs h₀ h₂ a b u v huv hGen hu hv

end ActualGaussianWeberSelectedBaseGenericFrob318
