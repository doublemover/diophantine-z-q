module
public import WeierstrassAffineFormCancellation318
public import WeierstrassAffineInvariantEquation318
public import IntrinsicDifferentialSectionPullback318
public import GluedNegation318
public section
noncomputable section
namespace WeierstrassInvariantNegation318
open AlgebraicGeometry CategoryTheory Opposite KaehlerDifferential
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
universe u
variable {R:Type u} [CommRing R] [IsDomain R] (A B:R)
  (hD:IsUnit (-16*(4*A^3+27*B^2)))
  (hy:(2:ShortAffineJacobian318.Ring A B)*ShortAffineJacobian318.y A B≠0)

lemma negative_equations {K M:Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (r:K) (a b d:M) (ha:(-r) • a=d) (hb:r • b=d):r • a=r • (-b):=by
  rw [smul_neg,hb]
  rw [neg_smul] at ha
  exact neg_eq_iff_eq_neg.mp ha

include hy

/-- Actual affine pullback by (x,y) -> (x,-y) sends the whole-affine
invariant differential to its negative, including the finite branch points. -/
theorem affine : AlgHomDifferential318.map (ChartNegation318.affineNeg A B)
    (WeierstrassAffineInvariant318.form A B hD)= -WeierstrassAffineInvariant318.form A B hD:=by
  apply WeierstrassAffineFormCancellation318.cancel_scalar A B hD
    (2*ShortAffineJacobian318.y A B) hy
  have he:=congrArg (AlgHomDifferential318.map (ChartNegation318.affineNeg A B))
    (WeierstrassAffineInvariantEquation318.equation A B hD)
  rw [AlgHomDifferential318.map_smul,AlgHomDifferential318.map_D,
    map_mul,map_ofNat,ChartNegation318.affineNeg_y,ChartNegation318.affineNeg_x] at he
  change ((2:ShortAffineJacobian318.Ring A B)* -ShortAffineJacobian318.y A B) •
    AlgHomDifferential318.map (ChartNegation318.affineNeg A B)
      (WeierstrassAffineInvariant318.form A B hD)=D R (ShortAffineJacobian318.Ring A B)
        (ShortAffineJacobian318.x A B) at he
  rw [show (2:ShortAffineJacobian318.Ring A B)* -ShortAffineJacobian318.y A B=
    -(2*ShortAffineJacobian318.y A B) by ring] at he
  exact negative_equations (M:=KaehlerDifferential R (ShortAffineJacobian318.Ring A B))
    _ _ _ _ he (WeierstrassAffineInvariantEquation318.equation A B hD)

end WeierstrassInvariantNegation318
