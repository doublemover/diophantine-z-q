module
public import LiteralWeierstrassPoints318
public section
noncomputable section
namespace RationalWeierstrassPoints318
open CategoryTheory AlgebraicGeometry AffineEquationFunctor318 AffineSchemeSolutions318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {K:Type} [Field K] [Algebra ℚ K]
abbrev FinitePoints:=LiteralWeierstrassPoints318.FinitePoints (K:=K)
abbrev solutionPoint:=LiteralWeierstrassPoints318.solutionPoint (K:=K)
abbrev equationFiniteEquiv:=LiteralWeierstrassPoints318.equationFiniteEquiv (K:=K)
/-- Arbitrary nonsingular rational short Weierstrass coefficients, without
an OpenJ ratio, twisting or unconstructed coefficient specialization. -/
@[expose] def model (A B:ℚ) (_hD:IsUnit (-16*(4*A^3+27*B^2))) : WeierstrassCurve.Affine K:=
  ⟨0,0,0,algebraMap ℚ K A,algebraMap ℚ K B⟩
variable (A B:ℚ) (hD:IsUnit (-16*(4*A^3+27*B^2)))
instance model_elliptic : (model (K:=K) A B hD).IsElliptic:=by
  constructor
  have h:IsUnit (-16*(4*(algebraMap ℚ K A)^3+27*(algebraMap ℚ K B)^2)):=by
    simpa only [map_neg,map_mul,map_add,map_pow,map_ofNat] using hD.map (algebraMap ℚ K)
  convert h using 1
  simp only [model,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring
include hD in
theorem solution_iff_equation (x y:K) :
    y^2-x^3-algebraMap ℚ K A*x-algebraMap ℚ K B=0 ↔ (model A B hD).Equation x y:=by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [model,zero_mul,add_zero]
  constructor <;> intro h <;> linear_combination h
@[expose] def fieldPointEquiv : SchemePoints (K:=K) A B ≃ FinitePoints (model (K:=K) A B hD):=
  (schemeSolutionEquiv A B).trans
    ((Equiv.subtypeEquivProp (by
      funext xy
      exact propext (solution_iff_equation A B hD xy.1 xy.2))).trans
      (equationFiniteEquiv (model A B hD)))
theorem fieldPointEquiv_coordinates (p:Solutions (S:=K) A B) :
    fieldPointEquiv A B hD ((schemeSolutionEquiv A B).symm p)=
      solutionPoint (model A B hD) ⟨p.val,(solution_iff_equation A B hD p.val.1 p.val.2).mp p.property⟩:=by
  simp only [fieldPointEquiv,Equiv.trans_apply,Equiv.apply_symm_apply]
  rfl
end RationalWeierstrassPoints318
