# Registered differential line over the actual Γ1 quotient

For N ≥ 5, this packet registers the actual differential-orbit fibers as a Mathlib complex `FiberBundle` and `VectorBundle`. It does not substitute a new unrelated product bundle.

- `DependentFiberBundle318`: the dependent total space of the fibers `projection⁻¹{b}` is explicitly homeomorphic to the original orbit quotient. The topology is transported through that exact equivalence. All local trivializations are the previously constructed actual quotient charts, and the full `FiberBundle` interface is proved.
- `FiberLinearStructure318`: a chosen genuine local frame transports the complex vector-space structure to each actual fiber. Every other frame is proved linear using the already established actual inverse derivative-square transition law. No frame-compatibility premise is supplied.
- `VectorBundleRegistration318`: proves a general rank-one operator-continuity lemma from actual joint chart continuity, then registers the full `VectorBundle ℂ ℂ` instance on these fibers.
- `RegisteredLine318`: proves complex fiber dimension one, identifies the registered zero with the geometric zero orbit, and proves nondegeneracy of the previously descended Petersson norm on the registered fibers.

The prior packet already proves that these same actual transition factors are holomorphic and exactly the cotangent-square chart factors. This packet does not yet register `ContMDiffVectorBundle ω`, or identify a global cotangent tensor/sheaf construction. Cusp compactification, extension across cusps, and the specified PEL/arithmetic model remain separate. No claim is made that arbitrary intermediate subgroups act freely.

Run `bash build-all.sh` with the sibling proof packets and installed Lean 4.35.0 workspace available. All modules and every declaration are checked with `-Ddebug.skipKernelTC=false`; only `propext`, `Classical.choice`, and `Quot.sound` are allowed. No admitted geometric premise or native oracle is added.
