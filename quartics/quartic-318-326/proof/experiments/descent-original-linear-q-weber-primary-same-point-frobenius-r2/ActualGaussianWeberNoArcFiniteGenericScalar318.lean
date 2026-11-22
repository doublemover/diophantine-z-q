module
public import ActualGaussianWeberOddNormGeneric318
public import ActualGaussianWeberGaussValuation318
public import ActualGaussianWeberReductionCoordinates318
public import ActualGaussianWeberStockReductionAdd318
public section
noncomputable section

namespace ActualGaussianWeberNoArcFiniteGenericScalar318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine Polynomial
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberQuadraticGenericChart318
open ActualGaussianWeberGaussLocalization318 ActualGaussianWeberGaussValuation318
open ActualGaussianWeberTranslationChart318 ActualGaussianWeberTranslationFunctionField318
open ActualGaussianWeberStockCoordinateHom318 ActualGaussianWeberPlaceEquivariance318
open ActualGaussianWeberGaussianScalarSpecialization318 ActualGaussianWeberStockReductionAdd318
open ActualGaussianWeberOddNormGeneric318 ActualGaussianWeberReductionCoordinates318
open ActualGaussianWeberQuarterTurn318

variable {K : Type*} [Field K] (V : ValuationSubring K)
variable [DecidableEq (FunctionField K)] [DecidableEq (FunctionField (ResidueField V))]
variable [DecidableEq (ResidueField (gauss V))]

/-- Only additive reduction and the literal chosen-root quarter-turn
are needed for the generic image. Inertia and prime-to-p torsion
injectivity are deliberately outside this cap producer. -/
theorem specialize_scalar_core [DecidableEq K] [DecidableEq (ResidueField V)]
    (hK : (2:K) ≠ 0) (hR : (2:ResidueField V) ≠ 0)
    (i : V) (hi : i^2 = -1) (a b : ℤ) (P : WP K) :
    specializeHom V hK hR (gaussian hK (V.subtype i) (chosen_square_generic V i hi) a b P) =
      gaussian hR (residue V i) (chosen_square_residue V i hi) a b
        (specializeHom V hK hR P) := by
  change specializeHom V hK hR (a • P + b • turn hK (V.subtype i) _ P) =
    a • specializeHom V hK hR P + b • turn hR (residue V i) _ (specializeHom V hK hR P)
  rw [map_add,map_zsmul,map_zsmul]
  have h := specialize_turn V hK hR i hi P
  change specializeHom V hK hR (turn hK (V.subtype i) _ P) =
    turn hR (residue V i) _ (specializeHom V hK hR P) at h
  rw [h]

theorem integral_chart_generic (c : Chart V) :
    (gauss V).subtype (integralChart V c)=genericBase V c := by
  change intoGeneric V (algebraMap (Chart V) (Local V) c)=_
  exact intoGeneric_algebraMap V c

theorem gauss_two_ne (h2 : (2:ResidueField V)≠0) :
    (2:ResidueField (gauss V))≠0 := by
  intro h
  apply function_two_ne (ResidueField V) h2
  have e := congrArg (gaussResidue V) h
  simpa only [map_ofNat,map_zero] using e

@[expose] def constChart : V→+*Chart V := (AdjoinRoot.of (relation V)).comp C

theorem mapped_const {R S : Type*} [CommRing R] [CommRing S] (f : R→+*S) (c : R) :
    mapChart f (AdjoinRoot.of (relation R) (C c))=AdjoinRoot.of (relation S) (C (f c)) := by
  simp only [mapChart,AdjoinRoot.map_of,coe_mapRingHom,map_C]

@[expose] def integral_i (i : V) : gauss V := integralChart V (constChart V i)

theorem integral_i_sq (i : V) (hi : i^2 = -1) : (integral_i V i)^2= -1 := by
  have h := congrArg ((integralChart V).comp (constChart V)) hi
  simpa only [RingHom.comp_apply,map_pow,map_neg,map_one,integral_i] using h

theorem integral_i_generic (i : V) :
    (gauss V).subtype (integral_i V i)=constGeneric K (V.subtype i) := by
  rw [integral_i,integral_chart_generic]
  simp only [genericBase,RingHom.comp_apply,constChart,mapped_const,constGeneric,fractionMap]

theorem integral_i_residue (i : V) :
    gaussResidue V (residue (gauss V) (integral_i V i))=
      constGeneric (ResidueField V) (residue V i) := by
  rw [integral_i,integral_chart_specialize]
  simp only [residueBase,RingHom.comp_apply,constChart,mapped_const,constGeneric,fractionMap]

/-- The tautological generic point goes to the tautological point
over the actual residue function field. Both coordinates are given
by integral chart generators; no geometric comparison is postulated. -/
theorem generic_point_specializes (hK : (2:K)≠0) (h2 : (2:ResidueField V)≠0) :
    coordinateHom (gaussResidue V).toRingHom (function_two_ne (ResidueField V) h2)
      (specialize (gauss V) (gauss_two_ne V h2) (genericPoint K hK)) =
      genericPoint (ResidueField V) h2 := by
  let a := integralChart V (xChart V)
  let b := integralChart V (yChart V)
  have ha : xGeneric K=(gauss V).subtype a := by
    change xGeneric K=(gauss V).subtype (integralChart V (xChart V))
    rw [integral_chart_generic]
    simp only [genericBase,RingHom.comp_apply,map_xChart,xGeneric,fractionMap]
  have hb : yGeneric K=(gauss V).subtype b := by
    change yGeneric K=(gauss V).subtype (integralChart V (yChart V))
    rw [integral_chart_generic]
    simp only [genericBase,RingHom.comp_apply,map_yChart,yGeneric,fractionMap]
  have har : gaussResidue V (residue (gauss V) a)=xGeneric (ResidueField V) := by
    change gaussResidue V (residue (gauss V) (integralChart V (xChart V)))=xGeneric (ResidueField V)
    rw [integral_chart_specialize]
    simp only [residueBase,RingHom.comp_apply,map_xChart,xGeneric,fractionMap]
  have hbr : gaussResidue V (residue (gauss V) b)=yGeneric (ResidueField V) := by
    change gaussResidue V (residue (gauss V) (integralChart V (yChart V)))=yGeneric (ResidueField V)
    rw [integral_chart_specialize]
    simp only [residueBase,RingHom.comp_apply,map_yChart,yGeneric,fractionMap]
  let hn := nonsing_of_equation (function_two_ne K hK) (equation_generic K)
  obtain ⟨hR,ee⟩ := reduction_through_coordinates (gauss V) (gauss_two_ne V h2) hn a b ha hb
  change onCurvePoint (gaussResidue V).toRingHom (function_two_ne (ResidueField V) h2)
    (specialize (gauss V) (gauss_two_ne V h2) (Point.some (xGeneric K) (yGeneric K) hn))=_
  rw [ee,point_some]
  exact ActualGaussianWeberStockCoordinateHom318.some_congr har hbr

/-- Actual same-place finiteness of the generic odd-norm Gaussian
scalar image. No degree or finiteness premise is used. The only
specialization used is the previously constructed stock reduction. -/
theorem scalar_generic_reduces_finite (hK : (2:K)≠0) (h2 : (2:ResidueField V)≠0)
    (i : V) (hi : i^2 = -1) (a b p : ℤ) (hN : a^2+b^2=p) (hp : Odd p) :
    let j := integral_i V i
    let hj := integral_i_sq V i hi
    let P := gaussian (function_two_ne K hK) ((gauss V).subtype j)
      (chosen_square_generic (gauss V) j hj) a b (genericPoint K hK)
    ∃ (x y : FunctionField K), ∃ h : (curve (FunctionField K)).toAffine.Nonsingular x y,
      P=Point.some x y h ∧ x∈gauss V ∧ ∃ z : Local V, intoGeneric V z=x := by
  dsimp only
  let j := integral_i V i
  have hj := integral_i_sq V i hi
  let hF := function_two_ne K hK
  let hR := gauss_two_ne V h2
  let hS := function_two_ne (ResidueField V) h2
  let hsub := chosen_square_generic (gauss V) j hj
  let hres := chosen_square_residue (gauss V) j hj
  let hj₀ : (constGeneric (ResidueField V) (residue V i))^2= -1 := by
    simpa only [map_pow,map_neg,map_one] using
      congrArg (constGeneric (ResidueField V)) (chosen_square_residue V i hi)
  let P := gaussian hF ((gauss V).subtype j) hsub a b (genericPoint K hK)
  let ρ := coordinateHom (gaussResidue V).toRingHom hS
  let s := specializeHom (gauss V) hF hR
  have hspec : s P = gaussian hR (residue (gauss V) j) hres a b (s (genericPoint K hK)) := by
    letI : DecidableEq (ResidueField (gauss (gauss V))) := Classical.decEq _
    exact specialize_scalar_core (gauss V) hF hR j hj a b (genericPoint K hK)
  have hC : ρ (gaussian hR (residue (gauss V) j) hres a b (s (genericPoint K hK))) =
      gaussian hS (constGeneric (ResidueField V) (residue V i)) hj₀ a b
        (ρ (s (genericPoint K hK))) :=
    coordinate_gaussian _ hR hS _ _ hres hj₀ (integral_i_residue V i) a b _
  have hgen : ρ (s (genericPoint K hK))=genericPoint (ResidueField V) h2 :=
    generic_point_specializes V hK h2
  have hNon : s P≠0 := by
    intro H
    have e := congrArg ρ hspec
    rw [hC,hgen,H,map_zero] at e
    exact odd_generic_nonorigin (ResidueField V) h2 (residue V i)
      (chosen_square_residue V i hi) a b p hN hp e.symm
  change ∃ (x y : FunctionField K), ∃ h : (curve (FunctionField K)).toAffine.Nonsingular x y,
    P=Point.some x y h ∧ x∈gauss V ∧ ∃ z : Local V, intoGeneric V z=x
  cases hP : P with
  | zero =>
    exact False.elim (hNon (by rw [hP] <;> rfl))
  | some x y h =>
    have hx : x∈gauss V := by
      by_contra hnx
      apply hNon
      rw [hP]
      exact (specialize_some_eq_zero (gauss V) hR h).mpr hnx
    exact ⟨x,y,h,rfl,hx,exists_local_of_mem V x hx⟩

end ActualGaussianWeberNoArcFiniteGenericScalar318
