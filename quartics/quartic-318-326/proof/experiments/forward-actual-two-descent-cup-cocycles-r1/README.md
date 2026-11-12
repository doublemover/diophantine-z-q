# Actual E[2] perfect pairing and locally constant cup cocycles

Status: source draft; hosted Lean check and fresh distinct recovery review pending. The 1178 native-dual-levels predecessor sources are byte-identical. Eight new sources, 563 lines, construct a perfect alternating binary pairing on the original geometric two-torsion, its actual square-one-unit-valued form, and locally constant cup cocycles with explicit bounding cochains and original field restriction.

The source carrier is the actual `closedTwoTorsion n` over the algebraic closure of a characteristic-zero field, using the original sign-coordinate equivalence. The construction covers every nonzero n. The target of `originalRootPairing` is the actual subgroup of units whose square is one. Perfectness is an additive equivalence with the full additive dual, not a cardinality assertion.

`originalCupCocycle` belongs to mathlib native abstract group cohomology. Local constancy is proved separately for the cochains and explicit self/skew bounding cochains. No continuous-H2/abstract-H2 comparison or Brauer interpretation is inferred. Restriction uses the original absolute Galois map and actual torsion coefficient transfer under any characteristic-zero field embedding, not independently chosen finite coordinates.

Not proved: identification with the geometric Weil pairing; local Kummer isotropy, local invariant maps, global reciprocity, Sha/Cassels–Tate duality, rational-rank selection, four rational twist-point pairs, or the full arithmetic theorem. Inherited global-duality hypotheses remain untouched.

Recovery note: intermediate seven-source drafts were preserved in the project recovery directory. The final eight-source text was reconstructed from retained authored text, including three reviewed fixes and the final perfect-pairing module. Metadata is freshly bound and does not claim byte identity with the lost prior APPLICATION. A distinct reviewer must rebind these exact bytes. Finite regression and structural admission are not Lean elaboration or mathematical acceptance.
