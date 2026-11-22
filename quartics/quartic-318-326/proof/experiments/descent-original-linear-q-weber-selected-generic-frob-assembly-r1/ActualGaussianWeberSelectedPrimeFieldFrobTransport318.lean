module
public import ActualGaussianWeberSelectedPrimeFieldChart318
public import ActualGaussianWeberOddNormGeneric318
public import Mathlib.Algebra.CharP.Frobenius
public section
noncomputable section

namespace ActualGaussianWeberSelectedPrimeFieldFrobTransport318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberSelectedPrimeFieldChart318
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberPlaceEquivariance318
open ActualGaussianWeberTranslationFunctionField318 ActualGaussianWeberOddNormGeneric318
open ActualGaussianWeberGaussianScalarSpecialization318 ActualGaussianWeberStockCoordinateHom318
open ActualGaussianWeberQuarterTurn318

attribute [local instance] Classical.decEq

theorem field_characteristic_along {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (p : ℕ) [CharP K p] : CharP L p := by
  refine ⟨fun n => ?_⟩
  have h : (n : L) = 0 ↔ (n : K) = 0 := by
    rw [← map_natCast f n, ← map_zero f, f.injective.eq_iff]
  exact h.trans (CharP.cast_eq_zero_iff K p n)

section Selected

variable {p : ℕ} [Fact p.Prime]
variable (s : ZMod p) (hs : s^2= -1)

local notation "V" => BasePlace s hs
local notation "k" => ResidueField (BasePlace s hs)
local notation "k₁" => ZMod p
local notation "L" => ActualGaussianWeberGaussLocalization318.FunctionField (ResidueField (BasePlace s hs))
local notation "L₁" => ActualGaussianWeberGaussLocalization318.FunctionField (ZMod p)
local notation "j" => residue (BasePlace s hs) (integralI s hs)

/-- The same generic point is carried by the stock point map on the
literal chosen-residue chart; only its scalar coefficients change. -/
theorem selected_generic_point_transport (h₀ : (2:k)≠0) (h₁ : (2:k₁)≠0) :
    coordinateHom (selectedField s hs) (function_two_ne k₁ h₁) (genericPoint k h₀)=
      genericPoint k₁ h₁ := by
  obtain ⟨_,hx,hy⟩ := selected_i_and_generic_coordinates s hs
  let f := selectedField s hs
  let H := function_two_ne k₁ h₁
  let hn := nonsing_of_equation (function_two_ne k h₀) (equation_generic k)
  change onCurvePoint f H (Point.some (xGeneric k) (yGeneric k) hn)=_
  rw [point_some f H hn]
  exact some_congr hx hy

/-- Transfer a same-point positive-coordinate assertion to the old
stock Frobenius interface over the actual signed prime field.
No descriptor, stationarity, pole, degree or unit theorem is imported. -/
theorem primefield_frobenius_of_base_powers (h₀ : (2:k)≠0) (h₁ : (2:k₁)≠0)
    (a b : ℤ) (u v : ActualGaussianWeberGaussLocalization318.FunctionField (ResidueField (BasePlace s hs)))
    (huv : WeierstrassCurve.Affine.Nonsingular
      (WeierstrassCurve.toAffine (ActualGaussianWeberHenselianPointMap318.curve
        (ActualGaussianWeberGaussLocalization318.FunctionField (ResidueField (BasePlace s hs))))) u v)
    (hGen : gaussian (function_two_ne k h₀) (constGeneric k j)
      (by simpa only [map_pow,map_neg,map_one] using
        congrArg (constGeneric k) (chosen_square_residue V (integralI s hs) (integralI_sq s hs)))
      a b (genericPoint k h₀)=
        (show WP (ActualGaussianWeberGaussLocalization318.FunctionField (ResidueField (BasePlace s hs))) from
          WeierstrassCurve.Affine.Point.some u v huv))
    (hu : u=(xGeneric k)^p) (hv : v=(yGeneric k)^p) :
    letI : CharP L₁ p := field_characteristic_along (constGeneric k₁) p
    gaussian (function_two_ne k₁ h₁) (constGeneric k₁ s)
      (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k₁) hs)
      a b (genericPoint k₁ h₁)=
      coordinateHom (frobenius L₁ p) (function_two_ne k₁ h₁) (genericPoint k₁ h₁) := by
  letI : CharP L₁ p := field_characteristic_along (constGeneric k₁) p
  let f := selectedField s hs
  let H₀ := function_two_ne k h₀
  let H₁ := function_two_ne k₁ h₁
  let Φ := coordinateHom f H₁
  let fr := frobenius L₁ p
  let z₀ := constGeneric k j
  let z₁ := constGeneric k₁ s
  have hi₀ : z₀^2= -1 := by
    simpa only [map_pow,map_neg,map_one] using
      congrArg (constGeneric k) (chosen_square_residue V (integralI s hs) (integralI_sq s hs))
  have hi₁ : z₁^2= -1 := by
    simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k₁) hs
  obtain ⟨hi,hx,hy⟩ := selected_i_and_generic_coordinates s hs
  have hz : f z₀=z₁ := hi
  have hCov := coordinate_gaussian f H₀ H₁ z₀ z₁ hi₀ hi₁ hz a b (genericPoint k h₀)
  change Φ (gaussian H₀ z₀ hi₀ a b (genericPoint k h₀))=
    gaussian H₁ z₁ hi₁ a b (Φ (genericPoint k h₀)) at hCov
  have hG : gaussian H₀ z₀ hi₀ a b (genericPoint k h₀)=Point.some u v huv := hGen
  have hP : Φ (genericPoint k h₀)=genericPoint k₁ h₁ :=
    selected_generic_point_transport s hs h₀ h₁
  rw [hG,hP] at hCov
  have hu' : f u=(xGeneric k₁)^p := by
    calc
      f u=f ((xGeneric k)^p) := congrArg f hu
      _ =(f (xGeneric k))^p := map_pow f _ _
      _ =(xGeneric k₁)^p := congrArg (fun w : L₁ => w^p) hx
  have hv' : f v=(yGeneric k₁)^p := by
    calc
      f v=f ((yGeneric k)^p) := congrArg f hv
      _ =(f (yGeneric k))^p := map_pow f _ _
      _ =(yGeneric k₁)^p := congrArg (fun w : L₁ => w^p) hy
  let hn := nonsing_of_equation H₁ (equation_generic k₁)
  have hFr : coordinateHom fr H₁ (genericPoint k₁ h₁)=
      Point.some ((xGeneric k₁)^p) ((yGeneric k₁)^p) (mapped_nonsingular fr H₁ hn) :=
    point_some fr H₁ hn
  calc
    _ = Φ (Point.some u v huv) := hCov.symm
    _ = Point.some (f u) (f v) (mapped_nonsingular f H₁ huv) := point_some f H₁ huv
    _ = _ := (some_congr hu' hv').trans hFr.symm

end Selected

end ActualGaussianWeberSelectedPrimeFieldFrobTransport318
