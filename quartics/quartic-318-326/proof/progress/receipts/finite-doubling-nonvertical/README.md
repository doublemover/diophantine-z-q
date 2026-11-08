# Entire finite tripling kernel

The original full rank-eight torsion scheme is now identified with the actual entire finite part of the literal completed tripling zero-fiber, with an explicit Scheme isomorphism and both inverse identities.

General-base results, with unit discriminant:
- `FiniteDoublingUnit318.two_y_unit`: if an actual finite point has an actual finite doubled output, 2y is a unit in the whole coefficient algebra.
- `FiniteDoublingOpenLift318.universal`: every such arbitrary Scheme test map uniquely factors through the genuine D(2y) open.
- `FiniteCompletedEqualizer318.isLimit`: the entire original rank-eight torsion scheme is the categorical equalizer of actual completed doubling and negation on the whole finite chart, with invertible 3.

Literal-base results, for every N:
- `LiteralFiniteKernel318.universal` and `isLimit`: every finite Scheme-valued point killed by actual tripling factors uniquely through the original torsion inclusion.
- `LiteralFiniteKernelFiber318.iso`: actual rank-eight torsion scheme isomorphism with the pullback of the zero section by completed tripling restricted to the entire finite chart. Both inverse witnesses and structural projections are checked.

Nilpotents are retained. Maximal quotients are used solely to detect invertibility of 2y: if it were a nonunit, a maximal quotient makes the finite point self-negative; the actual inverse diagram makes its double zero, contradicting its finite doubled output. No equality of Scheme morphisms is inferred from equality on field points. The resulting actual localization lift is extended uniquely to arbitrary Scheme tests through the open-immersion universal property.

Five sources passed strict kernel checks and the recursive audit passed 76 declarations, with only propext, Classical.choice and Quot.sound. No local full-chain replay. Hosted integration and independent review remain separate.

Not claimed: the entire completed tripling kernel, a zero-section/open-and-closed decomposition, general-base associativity, PEL identification, or the final arithmetic witness construction. Cancellation is consumed only over the literal base, exactly as proved by its source.
