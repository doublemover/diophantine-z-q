# Actual Galois character reconstruction of the contact field

This12-source candidate retains all eight frozen labeled-contact-field-
reconstruction-r2 sources byte-for-byte and adds four sources. No local Lean
build; hosted elaboration and fresh independent acceptance pending.

NormalBasisCharacterRadicals318 constructs a Fourier sum of the ORIGINAL
IsGalois.normalBasis orbit in the supplied field. Its coordinate at identity
is1, proving the character vector nonzero without any assumed eigenspace
nonvanishing. Reindexing the actual group computes its sign-character action.
Its square is fixed by EVERY original automorphism, so the exact original
Galois fixed-field theorem descends it to the original base field. A nontrivial
character gives a genuinely nonsquare radicand, by proving that a square
radicand would force the constructed vector to be fixed.

FourBinaryCharacters318 implements the actual four complementary characters
on (Z/2)^4, in the specified contact-basis ordering. Both multiplicativity and
order2 are proved. The chosen complementary coordinate flip gives value-1,
proving each character nontrivial in characteristic0. These coordinates are
NOT silently identified with the historical prime-divisor labels: an actual
labeled Galois-group isomorphism is required from the geometric producer.

ComplementaryFunctionRigidity318 proves the original four complementary
functions determine an algebra map on the entire original contact field.
Their signs, not just squares, are used. It then proves that any actual field
equivalence preserving them with the stated nonzero base-field scaling factors
intertwines a supplied geometric action with the OLD root-sign action. Thus
no new abstract equivariant map replaces the branch-reconstructed map.

GaloisCharacterContactReconstruction318 consumes the ORIGINAL finite Galois
extension L/Q(t) and a specified group isomorphism from its actual automorphisms
to the four labeled binary coordinates. It constructs all four actual roots
and nonsquare base radicands; degree16 follows from the actual Galois cardinal
theorem. The previously supplied root/degree inputs are therefore eliminated.
The terminal reconstruct theorem consumes only branch-parity equations for
these actual character functions, at EVERY prime polynomial, and concludes an
original contact-field equivalence with compatible rational twists.
reconstruct_equivariant proves the SAME equivalence intertwines EVERY actual
Galois automorphism with the original root-sign map in the supplied labels.

## Exact remaining geometric inputs

This is not a construction of the PEL curve, its canonical Galois quotient,
or its labeled branch divisor. Geometry must produce that original field and
labeled action, and prove the stated canonical num/denom parity from its local
orders. Every finite closed point, not only rational contacts, remains in the
parity quantifier. The global rational-function identity also controls infinity.
Fixed arithmetic twists still require the actual rational original-quotient
coefficient scalings, rather than equal j or merely isogenous Jacobians.
The published degree2 involution quotients and degree8 character quotients
remain distinct. Extending the genuine field equivalence to the actual proper
smooth curves remains a separate theorem application.

The target is the genus5 contact curve versus the maximal-level Shimura curve
X. The quaternionic abelian surface has dimension2 and is a FAMILY FIBER overX;
it is not the contact Jacobian. No represented Jacobian, PEL moduli realization,
universal family, polarization or isogeny is asserted here. The earlier exact
first-order Picard-kernel and norm decomposition remains a separate consumer.

Historical source/application evidence and its frozen sources are retained in
the predecessor APPLICATION/README; they are not promoted to Lean constructions.

Revision2 guards terminal reflexivity after the original normal-basis action rewrite, as independently requested. Eleven other sources exact, no mathematical change; hosted pending.
