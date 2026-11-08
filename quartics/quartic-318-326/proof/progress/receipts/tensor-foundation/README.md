# Genuine tensor square and actual local sections

Eight modules define the actual O-module tensor product by sheafification, prove its exact compatibility with actual open-immersion restriction, construct tensor functoriality and the tensor-unit isomorphism, and apply these to the actual contact normalization cotangent sheaf.

ContactBicanonicalSheaf318.bicanonical is the genuine Omega tensor_O Omega, and localFrame trivializes it on the already checked full five-chart open cover. ContactBicanonicalCoefficients318 defines explicit regular finite-branch and infinity coefficients using the actual inverted denominators; branchQ0_unit and infinityQ1_unit are proved. ContactBicanonicalLocalSections318.q0 and q1 are actual sections on every chart.

These are LOCAL sections. Their identification with the published rational quadratic differentials and their equality on whole intersections remain later theorems. This packet does not assert global bicanonical sections, a global cotangent or bicanonical trivialization, a PEL/Kodaira-Spencer identification, or a genus/degree theorem. In particular, a named local section is not being substituted for its missing global gluing proof.

The literal infinity convention used in the coefficient definitions is u=c_0/y_0 and t=c_0/u^2, verified against InfinityFieldCoordinates318 and InfinityParameters318.coefficient_shape. The exact tensor-frame normalization is next; the local regular coefficient definitions and unit proofs here do not silently assume that theorem.

The two initial sheafification modules were reconstructed from retained proof text after workspace replacement; original byte identity is not claimed for those two files. All eight final sources were freshly replayed with strict kernel checking, and the joined recursive audit with the five exact recovered contact predecessors passed: 13 modules / 209 declarations, of which 116 declarations belong to this eight-module packet. Only propext, Classical.choice, and Quot.sound occur as axiom roots. No copied or renamed Mathlib sources are included.
