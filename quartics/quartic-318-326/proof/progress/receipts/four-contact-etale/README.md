# Actual simultaneous four-contact etale cover

Three modules, 20 public theorems and 62 exhaustively audited declarations. All sources were freshly kernel-rebuilt with only `propext`, `Classical.choice` and `Quot.sound` recursively.

## Actual cover, roots and maps

The cover algebra is the actual fourfold tensor product of the four constructed unit quadratic root algebras, grouped as two pairs. It is finite free of exact rank 16 and genuinely faithfully flat. When two is invertible it is etale. Its actual spectrum map to the original base is finite, etale and surjective. Split factors are explicitly allowed.

The four actual generators satisfy their square equations. They determine every algebra map out of the cover, and every four-root tuple in an arbitrary commutative receiving algebra gives a unique such map. After multiplying by the prescribed uniformizer powers, the cover contains roots of all four even contacts. Every simultaneous field-valued four-root tuple with nonzero uniformizer image factors through it, not only one selected tuple.

For an actual DVR, four finite even canonical valuations give one common actual uniformizer and four actual units without a decomposition premise. This constructs the rank-16 etale cover and all four roots of the original contact elements. The generic all-points theorem assumes the actual coefficient map into the receiving field is injective, so it does not incorrectly divide by a uniformizer in a residue field.

Every prime of the actual etale cover is unramified with actual ramification index one. Every closed-fiber branch has derived domain/DVR structure and preserves all canonical source valuations. The global tensor algebra is not asserted to be a field or domain.

## Scope

This constructs an actual simultaneous etale root cover. It does not identify a geometric exponent-two source fiber with this cover, prove that a separately presented four-contact order has it as its integral closure, or assert connectedness or irreducibility. The actual global source cover, branch parameters and their even contact values must still be identified. Global geometric realization and the final end-to-end theorem remain unproved.

## Replay

Run `bash run.sh`. It strictly rebuilds the three modules and audits every imported declaration belonging to those modules, including generated equivalences and helpers. The pinned Mathlib cache and frozen sibling packets are used. Generated Lean objects are excluded from deliverables.
