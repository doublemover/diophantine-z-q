# Cofactor r7 actual algebra-jet evaluation-algebra repair

INACTIVE SOURCE CANDIDATE; no local Lean, new kernel acceptance or activation.

Own run43728390279 at published a28f35d4c2678cbcd9633b289a8d0dd510cc0f5f passes13 complete draft modules, including the repaired NormalizedCofactorFirstOrder318 in5.379s. It then fails NormalizedCofactorAlgebraJet318 in3.322s solely at line66: missing Algebra R[X] S. Three later roots remain unreached. No source declaration from the failed module is accepted separately, and FirstOrder passage is not a whole-packet pass.

The actual projection proof now installs Algebra R[X] S from the existing Polynomial.aeval T map. No caller assumption is added. The generator equality also states its RHS explicitly as f(generator), rather than an underscore elaborating to f.toRingHom(generator); this preventive proof-tail change matches the preceding actual FirstOrder failure/repair and preserves the identical function. All original signatures, arbitrary R-algebra target S, complete signed roots and coefficient data remain. Root_relation, cofactor scalar, first-order lift and its root/polynomial identities are unchanged.

The three later source consumers were read. They consume the same projection and derivation APIs; no identical native fieldPoint rewrite boundary justified a source change in them. Keep those3 roots unchanged/unreached, not alleged to pass. Exactly one source changes in proposed17-root compact r8;19baseline sources/36-source closure remain. No original geometry research added, no field/domain/unit restriction, no root/2 inversion or scalar cancellation, no budget/trust/option changes.

The later inactive obstruction closures retain historical source/verification boundaries and are not automatically accepted by this replay. No intrinsic dualizing, regular/maximal-model, proper-gluing, all-place or GeometricRealization assertion.
