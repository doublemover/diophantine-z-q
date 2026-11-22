module
public import ActualLSGOriginalFullUniformization318
public import ActualGaussianWeberComplexUniformizationFibres318
public section
noncomputable section

namespace ActualLSGOriginalPrimeFibres318

/-- Every fibre of the literal Gaussian scalar of prime norm on
the original complex point group has exactly that cardinality.
The actual positive-i uniformization is constructed, not supplied. -/
theorem original_complex_prime_fibres :
    ActualGaussianWeberComplexUniformizationFibres318.LiteralComplexFibres :=
  ActualGaussianWeberComplexUniformizationFibres318.literal_complex_fibres
    ActualLSGOriginalFullUniformization318.uniformization

end ActualLSGOriginalPrimeFibres318
