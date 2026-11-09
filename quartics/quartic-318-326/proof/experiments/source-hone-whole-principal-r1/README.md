# Whole-overlap principal-part reduction

This uncompiled six-source packet assembles the original eight-monomial infinity
basis and the actual coefficient principal-part lift. Hosted strict Lean checks,
recursive axiom auditing and independent acceptance remain pending. No local Lean
compilation was performed. The five dependency sources are exact copies, recorded
in COPY_BINDINGS.json; only ContactWholePrincipalReduction318 is new.

The new overlap_fraction theorem applies the already checked whole_localization
of the entire original overlap order over the original infinity order. Every
overlap element is an actual infinity-ring element times a power of the actual
inverse of u. It does not replace the whole ring with a monomial subring.

The reduction theorem expands that infinity-ring numerator in all eight original
ratio monomials. It applies coefficient_principal_reduction to each coefficient,
with the same pole order n. The result is a sum of eight principal terms R_i(u)/u^n
times those monomials, where degree R_i < n, plus the image of an explicitly
constructed element of the original infinity ring. The equation is in the actual
overlap ring, not merely in its field or an unidentified vector space.

The zero-pole case n=0 is retained: the WithBot degree bound forces each principal
polynomial to be zero. The regular witness is a finite sum of the eight actual
coefficient witnesses multiplied by the actual basis entries. No nonzero
coordinate, tensor character or coefficient is discarded.

This gives finite principal parts for each individual overlap element, but the
pole order is not uniformly bounded. It does not yet prove that five classes span
H1, nor that they are independent or coincide with the five quotient pullbacks.
The next consumer can kill the actual infinity-image remainder using the original
Mayer-Vietoris boundary. Further reduction modulo the original finite-chart image
and exact identification of the surviving quotient pullbacks remain open.

Reviewed source joins: SourceInfinityOverlap318.whole_localization uses exactly
InfinityOverlapLocalization318.toOpen and coordinate; the local algebra structure
here is that same ring map. ContactHOneOrderBases318.infinity_expansion covers the
complete ThreeIndex. ContactInfinityRegularFractions318 supplies identities for
every original localized infinity coefficient with the same principalTerm and
inverseU used here. Prior pending packets are not relabeled as checked.
