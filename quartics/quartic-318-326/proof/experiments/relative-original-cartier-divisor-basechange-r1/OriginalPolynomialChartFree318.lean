module
public import RelativeOriginalPolynomialAlgebra318
public section
noncomputable section
namespace OriginalPolynomialChartFree318
open scoped TensorProduct
universe u
variable (k R B : Type u) [CommRing k] [CommRing R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra (Polynomial k) B]
  [IsScalarTower k (Polynomial k) B] [Module.Free (Polynomial k) B]
attribute [local instance] Polynomial.algebra

/-- Freeness over the actual coefficient polynomial ring is transported
through the ORIGINAL polynomial pushout comparison, not a new action.
This preserves t on the finite chart and 1/t on the reciprocal chart. -/
instance free : Module.Free (Polynomial R) (R ⊗[k] B) :=
  Module.Free.of_basis (((Module.Free.chooseBasis (Polynomial k) B).baseChange (Polynomial R)).map
    (RelativeOriginalPolynomialAlgebra318.polynomialComparison k R B).toLinearEquiv)
end OriginalPolynomialChartFree318
