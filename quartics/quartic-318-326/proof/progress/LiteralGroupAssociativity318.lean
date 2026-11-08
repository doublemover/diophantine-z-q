module
public import CompletedAdditionAssociativity318
public import LiteralProductReduced318
public section
noncomputable section
namespace LiteralGroupAssociativity318
open AlgebraicGeometry
open CompletedAdditionTriple318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
/-- Associativity of the actual completed-curve multiplication over the original
literal arithmetic base, with the reducedness premise discharged. -/
theorem associative (N:ℕ) :
    leftAssociate (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) (OpenJAffineScheme318.discriminant_unit N)=
      rightAssociate (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) (OpenJAffineScheme318.discriminant_unit N) := by
  letI : IsReduced (triple (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) :=
    LiteralProductReduced318.triple_reduced N
  exact CompletedAdditionAssociativity318.associative_of_reduced N
end LiteralGroupAssociativity318
