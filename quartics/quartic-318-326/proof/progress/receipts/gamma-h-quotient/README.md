# Actual Gamma_H quotient and diamond comparison

Strict Lean 4.35 replay and exhaustive recursive axiom audit: PASS, 81 declarations in six producer modules. Only propext, Classical.choice and Quot.sound occur.

This packet constructs the actual congruence-group and topological diamond quotient required by the point-level modular convention.

- `GammaHGroup318` constructs Gamma_H as the actual inverse image of H under the actual lower-right unit-residue homomorphism on Gamma0. It proves the literal congruence conditions, the marking-orbit characterization, the Gamma1 inclusion, and the exact diamond kernel.
- `GammaHDiamond318` constructs an actual integral determinant-one lift of every unit using integer Bezout. It proves surjectivity of the actual diamond map and constructs the actual group quotient Gamma_H/Gamma1 isomorphism with H.
- `GammaHQuotient318` forms the genuine topological Gamma_H orbit quotient. It is Hausdorff, connected and second countable. The genuine forgetful map from the previously constructed Gamma1 quotient is continuous and surjective. Quotient equality is characterized by actual integral transport of the H-orbit of the marked elliptic point. Genuine j descends and agrees with the algebraic invariant of each actual normalized model.
- `GammaHAction318` constructs the actual H action on the existing Gamma1 quotient. Normality and independence of the chosen integral lift are proved using the exact diamond kernel. The action is continuous.
- `GammaHDiamondQuotient318.actualHomeomorph` identifies the actual finite H quotient of the existing source with the actual Gamma_H orbit quotient, using the genuine forgetful maps and their original quotient topologies. The comparison preserves genuine j.
- `GammaHMarking318` identifies scalar residue labels with actual multiplication of the elliptic marked point. Coordinate transport multiplies the canonical marking by the inverse of the lower-right diamond unit. Central minus one, when in H, is proved to act trivially on the actual analytic quotient.

## Exact boundary

The finite diamond action on the curve is not asserted free or faithful. In particular its central minus-one kernel is retained; the abstract group quotient cardinality must not be substituted for the degree of the effective geometric map. The topology is constructed without assuming absence of elliptic stabilizers.

This packet does not install a complex atlas on the Gamma_H quotient or construct its compactification. The separate gamma-h-cusp-action packet extends the actual action and forms the actual compact topological quotient. Neither packet supplies the relative primitive N-torsion scheme, algebraic moduli comparison, point-level rational model identification, or PEL/Shimura/Hodge/Arakelov identification.

## Replay

Run `bash build-all.sh` while holding the common exclusive heavy-compile lock. All six producer modules and an exhaustive import-all recursive axiom audit are rebuilt sequentially with `debug.skipKernelTC=false`. Public, private and generated declarations are checked. Imported predecessors use the pinned checked cache; this is not a full dependency-closure replay or an independent review.

The receipt whitelist binds the exact sources, build scripts, replay logs and predecessor receipts. Compiled artifacts and live lock-status logs are excluded. No shared repository, manuscript, branch or PR was changed.
