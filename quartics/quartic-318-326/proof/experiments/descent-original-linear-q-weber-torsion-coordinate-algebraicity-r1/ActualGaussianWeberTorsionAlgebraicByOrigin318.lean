module
public import ActualGaussianWeberArcFunctionEmbedding318
public import ActualGaussianWeberPowerSeriesArc318
public import ActualGaussianWeberValuedPolynomialPole318
public import ActualGaussianWeberOddNormGeneric318
public import ActualGaussianWeberFiniteAnchorTorsion318
public import Mathlib.RingTheory.Algebraic.Basic
public section
noncomputable section

namespace ActualGaussianWeberTorsionAlgebraicByOrigin318

open IsLocalRing Polynomial WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberPlaceEquivariance318
open ActualGaussianWeberStockCoordinateHom318 ActualGaussianWeberOddNormGeneric318
open ActualGaussianWeberGaussLocalization318 ActualGaussianWeberTranslationFunctionField318
open ActualGaussianWeberArcFunctionEmbedding318 ActualGaussianWeberPowerSeriesArc318
open ActualGaussianWeberValuedPolynomialPole318 ActualGaussianWeberFiniteAnchorTorsion318

attribute [local instance] Classical.decEq

private theorem actual_faithful_pair_point {K F : Type*} [Field K] [Field F]
    (c : K→+*F) (hK : (2:K)≠0) (hF : (2:F)≠0)
    (x y : F) (hn : (curve F).toAffine.Nonsingular x y)
    (hE : Function.Injective (eval₂RingHom c x)) :
    coordinateHom (arcEmbedding c x y ((literal_equation x y).mp hn.1) hE) hF
      (genericPoint K hK)=Point.some x y hn := by
  let he := (literal_equation x y).mp hn.1
  let e := arcEmbedding c x y he hE
  let hG := nonsing_of_equation (function_two_ne K hK) (equation_generic K)
  change onCurvePoint e hF (Point.some (xGeneric K) (yGeneric K) hG)=_
  rw [point_some e hF hG]
  exact some_congr (arcEmbedding_x c x y he hE) (arcEmbedding_y c x y he hE)

private theorem map_point_reflects_zero {K F : Type*} [Field K] [Field F]
    (f : K→+*F) (hF : (2:F)≠0) (P : WP K)
    (h : coordinateHom f hF P=0) : P=0 := by
  cases P with
  | zero => rfl
  | some x y hn =>
    change onCurvePoint f hF (Point.some x y hn)=(0:WP F) at h
    rw [point_some f hF hn] at h
    exact False.elim (Point.some_ne_zero _ h)

/-- The original generic point is not killed by any positive integer
in characteristic zero. A faithful evaluation at the actual formal
origin would otherwise give nonzero torsion in the reduction kernel. -/
theorem generic_not_positive_torsion (K : Type*) [Field K] [CharZero K]
    (hK : (2:K)≠0) (n : ℕ) (hn : 0<n) :
    n • genericPoint K hK≠0 := by
  intro h
  let V := FormalValuation K
  let hF := formal_two_ne K hK
  let hR := formal_residue_two_ne K hK
  obtain ⟨x,y,hxy,hOrigin,_⟩ := formal_origin_arc K hK
  have hx : x∉V := (specialize_some_eq_zero V hR hxy).mp hOrigin
  have hFaithful : Function.Injective (eval₂RingHom (constField K) x) :=
    evaluation_at_pole_injective V (constVal K) hx
  let f := arcEmbedding (constField K) x y ((literal_equation x y).mp hxy.1) hFaithful
  let G := coordinateHom f hF
  let P := Point.some x y hxy
  have hGP : G (genericPoint K hK)=P :=
    actual_faithful_pair_point (constField K) hK hF x y hxy hFaithful
  have hTorsion : n • P=0 := by
    rw [←hGP,←map_nsmul,h,map_zero]
  have hUnit : residue V (n:V)≠0 := by
    intro hN
    have hCast : (n:K)=0 := by
      simpa only [map_natCast,map_zero] using congrArg (residueFormal K) hN
    exact hn.ne' (Nat.cast_eq_zero.mp hCast)
  have hZero : P=Point.zero := kernel_torsion_zero V hF hR P hOrigin n hUnit hTorsion
  exact Point.some_ne_zero hxy hZero

/-- Affine coordinates of actual positive-level torsion on the
original curve are algebraic over the original characteristic-zero
base. No division polynomial, complex torsion cardinal, or separate
supplied endomorphism degree is needed. -/
theorem torsion_integral_coordinates_of_positive_level
    (K F : Type*) [Field K] [CharZero K] [Field F] [Algebra K F]
    (hK : (2:K)≠0) (hF : (2:F)≠0) (n : ℕ) (hn : 0<n)
    (x y : F) (hxy : (curve F).toAffine.Nonsingular x y)
    (hTorsion : n • Point.some x y hxy=0) :
    IsIntegral K x ∧ IsIntegral K y := by
  have hX : IsIntegral K x := by
    by_contra hNo
    have hTrans : Transcendental K x := fun hx => hNo hx.isIntegral
    have hFaithful : Function.Injective (eval₂RingHom (algebraMap K F) x) := by
      intro a b h
      apply (transcendental_iff_injective.mp hTrans)
      simpa only [Polynomial.aeval_def,coe_eval₂RingHom] using h
    let f := arcEmbedding (algebraMap K F) x y ((literal_equation x y).mp hxy.1) hFaithful
    let G := coordinateHom f hF
    have hGP : G (genericPoint K hK)=Point.some x y hxy :=
      actual_faithful_pair_point (algebraMap K F) hK hF x y hxy hFaithful
    apply generic_not_positive_torsion K hK n hn
    apply map_point_reflects_zero f hF
    change G (n • genericPoint K hK)=0
    rw [map_nsmul,hGP,hTorsion]
  refine ⟨hX,IsIntegral.of_pow (by decide : 0 < (2:ℕ)) ?_⟩
  rw [(literal_equation x y).mp hxy.1]
  exact (hX.pow 3).sub hX

end ActualGaussianWeberTorsionAlgebraicByOrigin318
