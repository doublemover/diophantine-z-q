module
public import GluedNegation318
public import RelativeChordPoints318
public section
noncomputable section
namespace NegationPoints318
open CategoryTheory AlgebraicGeometry ChartNegation318 GluedNegation318
open AffineEquationFunctor318 AffineSchemeSolutions318 LiteralWeierstrassPoints318 RelativeChordPoints318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Actual evaluation of the finite-chart Scheme involution. -/
theorem finite_evaluation {R K:Type u} [CommRing R] [CommRing K] [Algebra R K]
    (A B:R) (f:ShortAffineJacobian318.Ring A B →ₐ[R] K) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ finiteNeg A B=
      Spec.map (CommRingCat.ofHom (f.comp (affineNeg A B)).toRingHom) := by
  dsimp only [finiteNeg,ShortAffineScheme318.scheme]
  rw [←Spec.map_comp]
  rfl

/-- Exact genuine point-group negation on every field specialization of the literal source. -/
theorem actual_point_negation (N:ℕ) {K:Type} [Field K] [Algebra (OpenJModel318.Base N) K]
    (f:ShortAffineJacobian318.Ring (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
      →ₐ[OpenJModel318.Base N] K) :
    pointOfHom N (f.comp (affineNeg (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)))=
      -pointOfHom N f := by
  have ha1 : (model (K:=K) N).a₁=0 := by
    simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      OpenJModel318.integralModel,OpenJModel318.curve,map_zero]
  have ha3 : (model (K:=K) N).a₃=0 := by
    simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      OpenJModel318.integralModel,OpenJModel318.curve,map_zero]
  unfold pointOfHom solutionPoint
  simp only [ofHom,AlgHom.comp_apply,affineNeg_x,affineNeg_y,map_neg]
  change WeierstrassCurve.Affine.Point.some _ _ _ = -WeierstrassCurve.Affine.Point.some _ _ _
  rw [WeierstrassCurve.Affine.Point.neg_some,WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rfl
  · simp only [WeierstrassCurve.Affine.negY,ha1,ha3,zero_mul,sub_zero]

end NegationPoints318
