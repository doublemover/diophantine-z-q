# Contact proof recovery after the 2026-11-08 03:57 UTC workspace reset

Eight completed, unpublished Lean modules have been reconstructed. Six are exact byte matches against hashes independently captured by the bounded reviewer before the reset. The two fraction-field modules are reconstructed from full verbatim source tool output; no original individual file hashes survive in the current record, so fresh replay is required rather than claiming independent exact-byte verification.

Original completed packet receipts, now historical evidence only:
- published-character-schemes: 4016826f8c5c1823ffa864c277bcfaa1fe1a92673fd64fc3957e430dbee52ce3, two modules, 31 declarations.
- cubic-affine-comparison: 44ae84f069c07b3b8661a45123755178b3d4f8f7eb3a01ac0b3264ff47922397, four modules, 42 declarations.
- cubic-character-fraction: e198279d371a9372e7aa7ff911ac80e21d1ab0b3c9e27570ae7b24fba63b6ed5, two modules, 68 declarations.
Each had passed a fresh strict replay and recursive allowed-axiom audit before reset. New reconstructed source has not yet been replayed against the restored dependency/toolchain tree.

The bounded contact intrinsic review prose is also restored. Its original receipt was c3adcc8e45fc49805c17200cf7d36b1eb66cb4d9d657f9fb9a933ecb00f83227, bound to contact-intrinsic-differentials receipt 1065e5e59469e1561bba2213a482cfcc2c917f117f6516e02c9d92e267a2b4c0. A new review receipt must bind the actual recovered target files before use. Copies in review-evidence are exact-byte recovered predecessor-reviewed Hodge modules, supplied to that lane rather than counted among this lane's eight new modules.

The SourceCharacterAlgebra318 draft is unfinished. Its last invocation ended with errors and released heavy.lock at 03:56:47. The recovered draft includes the two intended corrections (explicit sourceTower type arguments; IntermediateField.subtype is already a RingHom). Those corrections were not compiled before reset. Do not count it as a completed theorem packet.

Next proof route: IsIntegralClosure.lift factors each actual cubic order through the whole SourceOrder inside the same original full field. This gives finite affine source-to-character morphisms. Composing the original unbranched source cover with the cubic relative-normalization map supplies normalizationDesc from the actual contact normalization to the actual cubic normalization over P1. IsFinite.of_comp should establish finiteness because the composition is the already proved finite contact map and the target normalization map is separated. The projective published model/Jacobian/PEL identifications remain separate.

Exact coordinate formulas from the checked cubic algebra construction: t maps to (u_i^2/C_i)x_pub + centroid_i; the three-root product maps to (u_i^3/C_i)y_pub, with C_i the complementary twist product and u_i=(630,2058,42,336). Hence classically dt/z=(1/u_i) dx_pub/y_pub; this differential deduction has not been separately formalized.

No shared repository, manuscript, branch, PR, or desktop was edited in this recovery lane. Central checkpoint owns restored dependency/toolchain setup and publication. All subsequent Lean work must hold the central heavy.lock, emit ACQUIRED inside flock, and cap each exploratory invocation at 180 seconds.
