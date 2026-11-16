# Actual normalized source-ring cofactor derivation and localization

Inactive two-module source draft, not kernel verified. No local Lean or active packet change.

`NormalizedCofactorAlgebraJet318` extends the integral cofactor construction to arbitrary actual R-algebra targets S. It constructs the whole original normalized-order map to dual numbers over S and proves complete projection compatibility with a specified actual algebra map. The source polynomial base remains R[X]; coefficients are mapped through the actual R-algebra structure, not silently changed to S[X]. All unit and characteristic assumptions remain absent for this construction.

`NormalizedCofactorSourceDerivation318` then takes S to be the normalized source ring A ITSELF, T its actual polynomial coordinate and z its actual four quotient generators. The square equations come from the actual quotient. The resulting native self-jet projects to id_A and extracts a genuine relative derivation R→A→A. The derivative of the actual coordinate is the full Jacobian minor M, and the root derivatives are the exact cofactors.

The same source derivation extends through the existing native localization-derivation construction to any actual localization L of A, with the original algebra structures and scalar towers explicit. It agrees on every A-element and kills the original coefficient base by the native relative-derivation law. Preservation of A or of the chosen localization is constructed through the codomain, not supplied as an unknown-function range predicate.

This is a source-ring derivation, NOT a tangent functional at the number-field point renamed as a function-field derivation. A fraction-field specialization still needs a genuine original-domain construction and the actual fraction-ring instance. Localization does not establish that the local ring is a DVR, normal, reduced over the arithmetic base, or part of the original maximal regular model. In particular the arithmetic uniformizer need not be a uniformizer of a ramified normalized source localization. Nothing here licenses the reduced-vertical prime-uniformizer lemmas without that extra actual geometry.

Remaining: specialization compatibility with the original point functional, actual original generic/model identification, normalization and regular/semistable local models at bad twists, the relative dualizing determinant/fundamental-class comparison, global section extension, KS210 and metrics. No dualizing line or maximal model is fabricated from a free target module, and no GeometricRealization is asserted.

The exact custom closure inherits the separately bound proof-binder overlay and nonunit-cofactor source batch. All hashes and API pins are source evidence only. Source review, static import checks and unchanged resource settings are not hosted kernel or compiled-axiom acceptance.
