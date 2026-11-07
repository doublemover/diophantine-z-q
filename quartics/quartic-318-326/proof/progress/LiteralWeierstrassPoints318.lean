module
public import AffineSchemeSolutions318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public section
noncomputable section
namespace LiteralWeierstrassPoints318
open CategoryTheory AlgebraicGeometry AffineEquationFunctor318 AffineSchemeSolutions318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
variable {K:Type} [Field K]

/-- All actual finite nonsingular points, excluding only the genuine point at infinity. -/
@[expose] def FinitePoints (W:WeierstrassCurve.Affine K) :=
  {P:W.Point // P ≠ .zero}

@[expose] def solutionPoint (W:WeierstrassCurve.Affine K) [W.IsElliptic]
    (p:{xy:K×K // W.Equation xy.1 xy.2}) : FinitePoints W :=
  ⟨WeierstrassCurve.Affine.Point.mk p.property,by intro h; cases h⟩

/-- No additional nonsingularity premise: the actual elliptic discriminant supplies it. -/
@[expose] def equationFiniteEquiv (W:WeierstrassCurve.Affine K) [W.IsElliptic] :
    {xy:K×K // W.Equation xy.1 xy.2} ≃ FinitePoints W :=
  Equiv.ofBijective (solutionPoint W) (by
    constructor
    · intro p q h
      have hh := congrArg Subtype.val h
      change WeierstrassCurve.Affine.Point.some _ _ _ =
        WeierstrassCurve.Affine.Point.some _ _ _ at hh
      have hxy := WeierstrassCurve.Affine.Point.some.inj hh
      exact Subtype.ext (Prod.ext hxy.1 hxy.2)
    · rintro ⟨P,hP⟩
      cases P with
      | zero => exact (hP rfl).elim
      | some x y h =>
        refine ⟨⟨(x,y),WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h⟩,?_⟩
        rfl)

variable (N:ℕ) [Algebra (OpenJModel318.Base N) K]

/-- The literal source Weierstrass model after the actual field specialization. -/
@[expose] def model : WeierstrassCurve.Affine K :=
  ((OpenJModel318.integralModel N).map (algebraMap (OpenJModel318.Base N) K)).toAffine

instance model_elliptic : (model (K:=K) N).IsElliptic := inferInstanceAs
  (((OpenJModel318.integralModel N).map (algebraMap (OpenJModel318.Base N) K)).IsElliptic)

/-- The actual quotient equation is precisely the field-specialized source Weierstrass equation. -/
theorem solution_iff_equation (x y:K) :
    y^2-x^3-algebraMap (OpenJModel318.Base N) K (OpenJAffineScheme318.A N)*x-
      algebraMap (OpenJModel318.Base N) K (OpenJAffineScheme318.B N)=0 ↔
    (model N).Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
    OpenJModel318.integralModel,OpenJModel318.curve,map_zero]
  change _ ↔ y^2+0*x*y+0*y=x^3+0*x^2+
    algebraMap (OpenJModel318.Base N) K (OpenJAffineScheme318.A N)*x+
    algebraMap (OpenJModel318.Base N) K (OpenJAffineScheme318.B N)
  simp only [zero_mul,add_zero]
  constructor <;> intro h <;> linear_combination h

/-- Genuine base-preserving field-valued affine Scheme points correspond exactly to finite
nonsingular points of the actual literal Weierstrass model. -/
@[expose] def fieldPointEquiv :
    SchemePoints (K:=K) (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≃
      FinitePoints (model (K:=K) N) :=
  (schemeSolutionEquiv _ _).trans
    ((Equiv.subtypeEquivProp (by
      funext xy
      exact propext (solution_iff_equation N xy.1 xy.2))).trans
      (equationFiniteEquiv (model N)))

/-- The equivalence sends the actual coordinate evaluation morphism to the same finite
Weierstrass coordinates; it is not an unspecified bijection. -/
theorem fieldPointEquiv_coordinates
    (p:Solutions (S:=K) (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) :
    fieldPointEquiv N ((schemeSolutionEquiv _ _).symm p) =
      solutionPoint (model N) ⟨p.val,(solution_iff_equation N p.val.1 p.val.2).mp p.property⟩ := by
  simp only [fieldPointEquiv,Equiv.trans_apply,Equiv.apply_symm_apply]
  rfl

end LiteralWeierstrassPoints318
