# Original nonunit Jacobian-cofactor jet and native comparison

Inactive source draft; no local Lean and no hosted/kernel acceptance. This batch advances the actual nonunit map needed before a dualizing comparison. It does NOT identify a cotangent lattice with a dualizing lattice or construct a maximal model.

## Actual nonunit construction

For the actual four equations z_i^2=d_i(T-a_i), `NormalizedCofactorFirstOrder318` uses M=product(2*z_i) and b_i=d_i*product_{j!=i}(2*z_j). The diagonal root-variable Jacobian block has determinant exactly M by the native Matrix determinant theorem. The full conormal identities z_i*b_i+b_i*z_i=d_i*M are proved with the actual finite-product factors.

These values construct an algebra homomorphism from the WHOLE normalized four-root order into integral dual numbers: T maps to (T,M), each signed root maps to (z_i,b_i). Projection equals the actual integral point on every ring element, not only the coordinate. A genuine native universal cotangent/fiber functional is extracted. Its dT value is M, not one. No division, unit2, unit root, unit twist or good-prime assumption is used for this integral construction. It also remains a well-defined map when M vanishes.

`FirstOrderEvaluationRescale318` proves exact derivative rescaling for every native universal differential and the entire tensor fiber. The scalar need not be an integral unit; no image equality is inferred merely from field invertibility.

`NormalizedCofactorFieldComparison318` proves that extension of the integral cofactor jet is the existing normalized field jet rescaled by the exact M, checking every polynomial and all four signed roots. It proves the entire fiber identity

    algebraMap(I(x)) = algebraMap(M) * E(x).

Here E is the actual existing DT=1 normalized field evaluator, not a supplied functional. Only the field roots' nonvanishing and characteristic zero are used for the field derivative formula. The nonunit factor is retained, yielding the precise scaled-integrality assertion, not unscaled integrality or equality of integral lattices.

`OriginalNormalizedCofactorProducer318` starts from original rational c,t, original nonzero parameters hn, the actual point field and finite place, irreducible pi, and an integral parameter T representing t. Existing signed normalization constructs u,e,sigma and f. Root values, square relations, field nonvanishing and the native integral cofactor functional are produced internally. No unit-quartic or unit2 premise remains. All original signs and square multipliers persist. The final evaluator is the SAME original normalized evaluator used in earlier original-section work; the misleadingly narrow historical namespace of that definition does not impose unit-quartic assumptions on the definition itself.

## What this does not prove

The free coefficient target of the cofactor map is NOT declared to be a dualizing sheaf. This draft has not constructed the relative dualizing complex or proved that the conormal determinant coefficient is its canonical fundamental-class map. It has not compared the normalized presentation to the actual original maximal regular/semistable model. Those are separate geometric obligations; an arbitrary normal or finite algebra is not a substitute.

The obstruction is concrete: in z^2=pi(T-a), cotangent d z has DT-normalized value pi/(2z), while the usual hypersurface dualizing expression dt/(2z) differs by nonunit pi. The draft keeps the corresponding Jacobian factors rather than canceling them in the integral ring. No assertion that either expression already represents the actual maximal-model line is made.

The existing VerticalDerivation/VerticalSection lemmas concern a derivation on the MODEL FUNCTION FIELD preserving a vertical DVR. The present native tangent functional is at the original NUMBER-FIELD point; these are different domains. It is not substituted for that function-field derivation. Producing an actual integral source-ring derivation and extending it to the actual model/function-field/local rings is a separate step.

Still required: actual determinant/dualizing identification, original generic/sheaf tensor-fiber compatibility, comparison with the original maximal model at bad twists, reciprocal integral charts, integral q0/q1 extension in that line, and the actual KS map/210 image and metrics. The existing classical maximal-KS prose receipt is not treated as a Lean construction or substituted for these maps. No GeometricRealization or final height theorem follows here.

## Verification boundary

The closure uses the separately frozen explicit-proof-binder overlay for RingJetScalarExtension318.projection and IntegralUnitRootCotangent318.projection, retaining hL and hf/hr respectively. Earlier Library envelopes are unchanged; those corrected dependencies are bound in this current application. New cofactor projection and rescale projection also retain their proof-only hf/hr and hL.

Four new source modules, exact custom-import closure, original source hashes, official Mathlib API pins and independent source review form a recoverable draft. No active packet or resource/trust options change. Static hashing/import checks are not kernel checking or compiled-axiom audits.
