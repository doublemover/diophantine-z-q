# Actual holomorphic differential line registration

For N ≥ 5, this packet registers the actual differential-orbit line as `ContMDiffVectorBundle ω ℂ` on the constructed complex Γ1(N) quotient. Its dependent total space, already explicitly homeomorphic to the genuine orbit quotient, is thereby an actual complex analytic manifold.

- `HolomorphicLineFactor318` proves the actual inverse-square chart-derivative factors are holomorphic as functions on the genuine quotient manifold. It uses the already proved holomorphic inverse sheets and actual chart overlap domains.
- `LinearCocycleBinding318` identifies the registered continuous-linear coordinate change with scalar multiplication by that exact factor. Actual inverse trivializations are bound back to the genuine orbit frame maps.
- `HolomorphicLineRegistration318` constructs the full Mathlib holomorphic vector-bundle class and derives the actual total-space complex manifold.

No analytic transition function, derivative, manifold chart or vector-bundle structure is supplied as an unproved premise. The actual cotangent-square transition rule is proved upstream. Identification with a separate global cotangent tensor/sheaf construction, extension over cusp compactification, and the specified PEL/arithmetic curve/model remain distinct tasks. This packet is only for the free Γ1(N) quotient with N ≥ 5.

Replay: `bash build-all.sh`. All declarations are checked with `-Ddebug.skipKernelTC=false`, allowing only propext, Classical.choice and Quot.sound.
