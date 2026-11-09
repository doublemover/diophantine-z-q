# Application contract: actual scheme sheaf data to affine reconstruction

Draft only. Exact bindings and producer provenance accompany this contract.

1. **Required inputs.** The retained geometric affine consumer requires an
   original line and sheaf overlap map on the tensor-spectrum nerve, together
   with its exact geometric diagonal and triple laws. The new consumer takes
   an original actual scheme fiber-product overlap and its actual geometric
   laws. The required tensor geometric laws are proved through canonical
   sheaf transport; neither those laws nor module coalgebra laws are premises.
2. **Constructed objects.** The double/triple objects are precisely
   ActualOverlapDiagram318.Double and Triple for the original Spec algebra map.
   Their tensor-spectrum comparisons are the previously explicit mutually
   inverse scheme maps. Overlap transport uses actual Scheme.Modules.pullback
   and the original PullbackPathComposition318.iso at both endpoints. The
   output line/pullbackIso are the retained actual affine reconstruction maps.
3. **Coverage.** Canonical transport works for arbitrary schemes, maps and
   original module-sheaf morphisms. The nerve comparison works for arbitrary
   commutative rings. Faithful flatness is introduced only at the final affine
   line reconstruction. No field, reducedness, generic-point, closed-point or
   finite-type restriction replaces the actual full objects or covers.
4. **Transition directions.** Each actual sheaf edge is inverse first canonical
   path comparison, actual pulled-back overlap, forward second comparison.
   The commuting square compares tripleInverse then actual pair with tensor
   pair then doubleInverse. Actual labels01,12,02 match tensor12,23,13.
   The actual diagonal is normalized to Spec.map(identity), transported through
   the actual diagonal/tensor multiplication square, then denormalized with
   the original identity comparison in the exact prior consumer's direction.
5. **Hypothesis checks.** The generic successive-transport lemma derives its
   endpoint squares from two applications of accepted path associativity; the
   actual composition comparison's naturality gives the transported map.
   Commuting-square transport follows by composing both routes to the same
   actual named composite. The actual nerve pair/vertex and diagonal equations
   discharge every square input. Preservation of composition gives the triple
   law, and preservation of identity gives the normalized diagonal law.
6. **Consumer identity.** affine_path proves equality with the retained
   OriginalLineNamedComparison318.pullbackAlong, so the transported edge is
   literally OriginalGeometricEdge318.edge. The transported laws are precisely
   OriginalGeometricTriple318.Cocycle and OriginalGeometricDiagonal318.Diagonal.
   ActualAffineLineReconstruction318 then calls the original reconstruction
   with the actual transported input overlap and returns a pullbackIso ending
   at the unchanged L.object, not a new line model or class representative.
7. **Scalars and normalization.** The original canonical equality and
   composition comparisons remain at all endpoints. The named Spec identity
   transport is explicit on the diagonal. No automorphism, scalar correction,
   tensor-action replacement, degree, norm, Euler factor or polarization is
   added or discarded. All final equations are actual sheaf-map equalities.
8. **Downstream boundary.** Actual scheme fiber-product sheaf laws now supply
   the geometric tensor laws used for affine line existence. The proof that
   the displayed pullbackIso is a morphism in the independently packaged
   general geometric descent category remains separate. Different base-chart
   compatibility, arbitrary-cover and rigidification gluing, Picard
   identification, degree zero, representability and the full arithmetic
   theorem are not claimed. No arithmetic premise or historical verdict changes.
9. **Evidence and acceptance.** Five new sources and45 exact predecessor copies
   are bound, preserving all previously frozen bytes. Producer validation is
   pending in the current hosted sequence and is not assumed. Static checks
   and audit-history self-tests pass. No local Lean ran; complete50-source
   hosted strict checking, recursive audit and independent acceptance remain
   pending. This application contract does not grant acceptance.

## Revision r2: explicit defining upstream import

Run42579034823 at c2b05cf passed15 predecessor modules, including the scalar
composition and restricted coordinate repairs, then found Adjunction.toComonad
absent from AffineTripleOverlapMaps318's import closure. This revision adds
only the exact pinned Mathlib.CategoryTheory.Monad.Adjunction public import.
Forty-nine source files remain byte-identical, and the revised source has no
mathematical body change. The original50-source packet is preserved, and exact
producer failure evidence is retained here. Full hosted replay/audit remains
pending; no local Lean ran.
