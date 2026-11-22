module
public import ActualGaussianWeberArcFunctionEmbedding318
public import ActualGaussianWeberOddNormGeneric318
public section
noncomputable section

namespace ActualGaussianWeberScalarOnArc318

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberQuadraticGenericChart318
open ActualGaussianWeberGaussLocalization318 ActualGaussianWeberTranslationFunctionField318
open ActualGaussianWeberStockCoordinateHom318 ActualGaussianWeberGaussianScalarSpecialization318
open ActualGaussianWeberPlaceEquivariance318 (onCurvePoint)
open ActualGaussianWeberOddNormGeneric318 ActualGaussianWeberArcFunctionEmbedding318

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq F] [DecidableEq (FunctionField k)]

/-- The actual generic Gaussian scalar's abscissa can be evaluated
on any nonconstant arc of the same curve with the same base embedding.
The abscissa is not merely characterized pointwise on selected probes. -/
theorem scalar_rational_x_on_arc (c : k→+*F) (h2k : (2:k)≠0) (h2F : (2:F)≠0)
    (i : k) (hi : i^2= -1) (a b : ℤ) (A B : k[X])
    (x y : F) (he : y^2=x^3-x) (hx : Function.Injective (eval₂RingHom c x))
    (u v : FunctionField k) (huv : (curve (FunctionField k)).toAffine.Nonsingular u v)
    (hGen : gaussian (function_two_ne k h2k) (constGeneric k i)
      (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi)
      a b (genericPoint k h2k)=Point.some u v huv)
    (hRat : u=fractionMap k (AdjoinRoot.of (relation k) A) /
      fractionMap k (AdjoinRoot.of (relation k) B)) :
    ∃ q : F, ∃ h : (curve F).toAffine.Nonsingular (A.eval₂ c x/B.eval₂ c x) q,
      gaussian h2F (c i)
        (by simpa only [map_pow,map_neg,map_one] using congrArg c hi)
        a b (Point.some x y (nonsing_of_equation h2F he))=
      Point.some (A.eval₂ c x/B.eval₂ c x) q h := by
  let e := arcEmbedding c x y he hx
  let S := coordinateHom e h2F
  let hk := function_two_ne k h2k
  let hiGen : (constGeneric k i)^2= -1 := by
    simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi
  let hiF : (c i)^2= -1 := by simpa only [map_pow,map_neg,map_one] using congrArg c hi
  have hg : S (genericPoint k h2k)=Point.some x y (nonsing_of_equation h2F he) := by
    change onCurvePoint e h2F (Point.some (xGeneric k) (yGeneric k)
      (nonsing_of_equation hk (equation_generic k)))=_
    rw [point_some]
    exact ActualGaussianWeberStockCoordinateHom318.some_congr
      (arcEmbedding_x c x y he hx) (arcEmbedding_y c x y he hx)
  have hC := coordinate_gaussian e hk h2F (constGeneric k i) (c i) hiGen hiF
    (arcEmbedding_const c x y he hx i) a b (genericPoint k h2k)
  have hC' : S (gaussian hk (constGeneric k i) hiGen a b (genericPoint k h2k))=
      gaussian h2F (c i) hiF a b (S (genericPoint k h2k)) := hC
  rw [hGen,hg] at hC'
  have heval : e u=A.eval₂ c x/B.eval₂ c x := by
    rw [hRat,map_div₀]
    exact congrArg₂ (· / ·) (arcEmbedding_polynomial c x y he hx A)
      (arcEmbedding_polynomial c x y he hx B)
  change onCurvePoint e h2F (Point.some u v huv)=_ at hC'
  rw [point_some] at hC'
  let hV := mapped_nonsingular e h2F huv
  have hNew : (curve F).toAffine.Nonsingular (A.eval₂ c x/B.eval₂ c x) (e v) := by
    rw [←heval]
    exact hV
  exact ⟨e v,hNew,hC'.symm.trans
    (ActualGaussianWeberStockCoordinateHom318.some_congr heval rfl)⟩

end ActualGaussianWeberScalarOnArc318
