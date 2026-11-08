# Bounded integration review: arithmetic twists and infinity field map

This review is by the checkpoint integrator, distinct from the packet author. It checks exact endpoint hypotheses and the interpretation of the integrated source, not an independent reproof of every internal lemma or the entire arithmetic theorem. The integrated fresh kernel replay and recursive audit are recorded separately in the checkpoint receipt.

## Arithmetic field identification

The endpoint `SourceTwistFieldEquiv318.source_equiv_of_published_scalings` quantifies arbitrary nonzero rational twists. For each complementary index it explicitly requires a nonzero rational coordinate scale relating both the depressed cubic A coefficient by the fourth power and the B coefficient by the sixth power to the published coefficient pair. These four scaling hypotheses are not discharged by this packet.

The preceding squareclass recovery uses those hypotheses to obtain the fixed four classes (-14,-6,42,-21). The endpoint then constructs a genuine Q(t)-algebra equivalence by explicit quadratic root-scaling maps and their tensor product; it does not take a field isomorphism as an input. Its conclusion is still conditional on the four rational coefficient scalings. The separate source-geometric review addresses the informal Jacobian argument within stated geometric inputs and is not a formal PEL construction. No current use in the checkpoint supplies unconditional RefinedGeometricRealization from this result.

## Infinity map and coordinate field

The original contact field remains the four-root field over the source variable t. The new rational-function variable acts on it through the proved transcendental infinity coordinate u, not through the original t-algebra structure. `InfinityFieldMap318.parameter_at_coordinate` verifies the quadratic parameter identities for that changed base map. Its three actual root maps send the new roots to the ratios of original roots, and their tensor product constructs `fieldHom`.

`fieldHom_injective` uses the already constructed field structure on the degree-eight source of this homomorphism. `fieldHom_on_base` records the exact changed rational-function action. The source includes neither a surjectivity theorem nor an algebra equivalence with the entire original field. The finite-free rank-eight etale domain neighborhood containing u=0 is a local algebra construction; the packet does not glue it to the finite charts or produce a global proper model.

## Disposition

The endpoint signatures support the limited checkpoint descriptions. The actual PEL/Jacobian input, infinity-map surjectivity, global gluing, controlled integral reduction and unconditional arithmetic endpoints remain open. Earlier historical arguments have not been classified as absent or newly repaired here. The manuscript and polynomial files are unchanged.
