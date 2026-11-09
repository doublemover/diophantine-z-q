# Actual Mayer–Vietoris kernel and source-H1 quotient: revision 1

This is a pending hosted-check packet, not a verified result. No local Lean
compiler, build or axiom audit was run. It retains the 30 byte-identical sources
of `source-mayer-vietoris-20261109` and carries forward its distinct non-author
acceptance only for that unchanged predecessor scope. The four kernel-continuation
sources are still subject to a fresh strict check and recursive axiom audit.

## Exact changes from the older unfrozen kernel continuation

- `LocalCohomologyRestriction318` is byte-identical. Its original status reports
  an individual strict check; this is not evidence of checking the later kernel.
- `MayerVietorisSectionKernel318` gains a direct public import of the pinned
  `Mathlib.Algebra.Homology.ShortComplex.Ab`, which supplies the exact
  `ShortComplex.ab_exact_iff` API it uses. Its theorem statements and proofs
  are unchanged. This makes the dependency explicit rather than relying on a
  possible transitive import. It is not a claimed correction of a recorded error.
- `AffineCoverHOneQuotient318` is byte-identical to the older draft.
- `ActualSourceHOneQuotient318` keeps its existing equivalence and component
  identity and adds explicit zero/equality criteria for original overlap
  representatives: boundary x = boundary y exactly when x-y belongs to the range
  of the original finite/infinity restriction-difference map.

`COPY_BINDINGS.json` records every predecessor, original draft and candidate hash,
so a copied earlier draft is never misrepresented as newly checked. No old source,
receipt, review or accepted progress manifest was modified.

## Source and consumer comparison

The actual Ext Mayer–Vietoris sequence is exact at its original local H0 overlap
term. Its preceding map is the difference, not the sum, of the two original
restriction maps. The explicit local-H0 section equivalence is natural for these
open restriction maps. Transporting exactness along that equivalence and the
already checked terminal-local-to-global equivalence gives precisely the kernel
of the existing original global-H1 boundary. Quotienting by that kernel and using
the existing boundary-surjectivity theorem yields the intended additive quotient
equivalence, retaining the actual boundary on each representative.

The consumer uses the exact source `ContactGlobalSmooth318.Model units`, the full
finite and infinity chart ranges, their original affine witnesses, and the actual
full-cover equality. Its codomain is the same `SourceHOne` used by every original
quotient pullback and transfer. No differential space, tangent space, artificial
cohomology carrier, shortened chart or unproved dimension is substituted.

## Pinned API inspection and remaining elaboration risks

The producer read the exact pinned Mathlib source at commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`:

- `Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean`: the sequence
  has arrows toBiprod, fromBiprod, delta; fromBiprod on the product is restriction
  from the first chart minus restriction from the second.
- `Mathlib/Algebra/Homology/ExactSequence.lean`: `.exact 1` is the adjacent
  fromBiprod/delta short complex, not a different position in the sequence.
- `Mathlib/Algebra/Homology/ShortComplex/Ab.lean`: `ab_exact_iff` has the required
  elementwise kernel-to-image direction.
- `Mathlib/GroupTheory/QuotientGroup/Basic.lean`: the additive first-isomorphism
  API uses the actual surjection, and equality of subgroups changes only the
  quotient relation. Both induced maps retain each original representative.

Possible elaboration pressure points remain: reducing the derived sequence's
short complex to the displayed one; the categorical biproduct/additive-product
coercions; reducing the concrete opens square in restriction naturality; and
strict-module transparency in the representative identities. Source inspection
is not a compiler pass. CI must settle these points before a success claim.

No coordinate computation of the overlap quotient, rational H1 dimension,
fivefold H1 spanning, Picard tangent comparison, Serre duality or isogeny is
claimed. The explicit quotient is a concrete next input to such a calculation,
not the calculation itself. Independent acceptance of the four-source extension
remains pending. Shared experiment activation belongs to the coordinator.
