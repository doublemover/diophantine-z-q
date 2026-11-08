# Actual mixed-input addition and regular both-infinity chart

This packet advances the actual relative short-Weierstrass addition over an arbitrary commutative coefficient ring. The whole mixed-input law assumes exactly the unit discriminant needed by the prior finite-input law. Its literal OpenJ specialization is unconditional.

`MixedInputLocal318` constructs the finite-first localization D(v), its genuine finite-pair map, and its addition. It proves compatibility with the existing infinity-input chart on D(hv), and then over every coefficient algebra by the actual localization universal property. No field-point, reducedness, or density argument is used.

`MixedAdditionGluing318` proves equality on the categorical pullbacks by the actual tensor-product comparison, glues the two local maps using `Scheme.OpenCover.glueMorphisms`, and transports the result to the entire infinity-chart times finite-chart relative fiber product. Exact restrictions, preservation of the coefficient base, and the genuine infinity-section identity on the whole finite chart are proved. `SymmetricMixedAddition318` transports through actual fiber-product symmetry to the opposite mixed product and proves its base compatibility and genuine right identity.

The recovered both-infinity modules construct a regular addition morphism on D(Q*C), with exact ring-level Vieta proofs that retain tangent and nilpotent directions. D(V1), D(V2), and D(Q*C) cover the whole infinity-times-infinity product. The repaired `BothInfinityOrigin318` proves the original-base pair of infinity sections lifts to this regular chart and maps to infinity. The original incomplete source had a localization proof-binder error; its repaired source is included here. `BothInfinityUnit318` proves left and right coordinate unit identities over every coefficient algebra. It does not assert whole infinity input unit sections factor through that regular chart.

## Boundary

This packet does not glue the three opens of the both-infinity input product, prove compatibility of the chart-product laws on every global overlap, construct a full multiplication on the completed curve, prove the global group axioms, construct multiplication by N, or construct relative primitive torsion schemes. The symmetric mixed map is obtained by transport; this alone does not prove agreement with the finite-finite law on their overlap.

## Replay

Run `bash run.sh`. Lean 4.35.0 with `debug.skipKernelTC=false`. Mathlib checkout is inherited from the existing project toolchain. Ten modules and all their public/private declarations are recursively audited, allowing only `propext`, `Classical.choice`, and `Quot.sound`. This checks imported proof dependencies recursively; it is not a fresh rebuild of every upstream module. The receipt binds source files, scripts, logs, and frozen upstream receipt hashes.
