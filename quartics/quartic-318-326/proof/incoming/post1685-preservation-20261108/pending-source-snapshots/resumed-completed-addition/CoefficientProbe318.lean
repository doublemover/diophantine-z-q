module
public import WeierstrassCoefficientMap318
public import FiniteAdditionGluing318
public section
noncomputable section
namespace FinitePairCoefficient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeChordAlgebra318 (PairRing)
open InfinityAdditionAlgebra318
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
local notation "a" => algebraMap R S
@[expose] def pair (A B:R) : PairRing A B →ₐ[R] PairRing (a A) (a B) :=
  Algebra.TensorProduct.lift (R:=R) (S:=R)
    (((RelativeChordAlgebra318.leftPair (a A) (a B)).restrictScalars R).comp (AffineBaseChange318.coefficientMap (S:=S) A B))
    (((RelativeChordAlgebra318.rightPair (a A) (a B)).restrictScalars R).comp (AffineBaseChange318.coefficientMap (S:=S) A B))
    (by intro x y; exact Commute.all (α:=PairRing (a A) (a B)) _ _)

end FinitePairCoefficient318
