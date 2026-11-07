module
public import DualPrimeParity318
public import SquareFactorization318
public section
namespace GlobalDualSquare318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
set_option maxHeartbeats 0

/-- The actual dual two-isogeny arithmetic assertion is unconditional:
every nonzero abscissa on Y²=X³+4(3−sqrt2)²X is a square in Q(sqrt2). -/
theorem dual_square_abscissa : GlobalSquareHalving318.DualSquareAbscissa := by
  intro X Y he hX
  exact SquareFactorization318.positive_even_square X hX
    (DualLocalArithmetic318.dual_real_positive X Y he hX)
    (fun q hq m hm=>DualPrimeParity318.dual_prime_even q hq X Y m hm he)

/-- Actual square-abscissa source points admit actual group halves, with
no remaining dual-descent assumption. -/
theorem square_halving (h j:K) (hj:j^2=h^4-D) :
    ∃Q:E.Point,Q+Q=Point.some (h^2) (h*j) (RootPointAlgebra318.square_point h j hj) :=
  GlobalSquareHalving318.square_halving dual_square_abscissa h j hj

end GlobalDualSquare318
#print axioms GlobalDualSquare318.dual_square_abscissa
#print axioms GlobalDualSquare318.square_halving
