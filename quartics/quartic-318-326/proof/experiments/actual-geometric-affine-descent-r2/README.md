# Original scheme fiber-product sheaf data reconstructs an affine line

This50-source draft joins the actual categorical scheme Cech nerve to the
geometric affine reconstruction. Five new sources derive transport of the
actual sheaf diagonal/triple equations through the explicit double/triple
nerve isomorphisms. No tensor law or module coalgebra law is added as a premise.

## End-to-end consumer

Start with a faithfully flat commutative R-algebra S, the unchanged original
line L on Spec S, and an actual sheaf morphism between the two pullbacks of L
on the actual scheme double fiber product. Assume its actual scheme triple
cocycle and actual diagonal identity, with canonical sheaf path normalizations.

`ActualAffineLineReconstruction318.line` constructs a line on Spec R.
`pullbackIso` is an actual isomorphism from its original scheme pullback to
L.object. The construction derives the tensor-spectrum sheaf laws, then the
module evaluation/cocycle laws, then the original scalar-extension coalgebra
laws before invoking the existing faithfully flat rank-one reconstruction.

## New transport argument

1. `SheafPathTransport318` proves that normalized actual sheaf pullback preserves
   identities and compositions, respects successive pullbacks and actual
   commuting squares. Successive transport is derived from the accepted
   PullbackPathComposition318.assoc and actual composition naturality.
2. `ActualAffineSheafData318` defines the actual fiber-product sheaf cocycle.
   Its diagonal is canonically normalized to the named Spec identity map;
   no module or scalar hypothesis is included.
3. `ActualAffineTensorTransport318` identifies the original affine named path
   comparison with the generic canonical sheaf path comparison. Each actual
   pair-map square then transports its actual normalized sheaf edge to the
   exact retained tensor-spectrum edge.
4. `ActualAffineTensorLaws318` uses all three exact pair squares for the cocycle.
   The actual diagonal/tensor multiplication square gives the normalized
   diagonal law; cancelling the normalization and restoring the original
   identity comparison gives precisely the previous geometric diagonal input.
5. `ActualAffineLineReconstruction318` invokes the existing reconstruction on
   these derived geometric laws and retains the unchanged input line object.

## Remaining boundary

The actual scheme fiber-product/tensor-spectrum join is now implemented in
source. Full hosted validation is pending. The construction does not yet prove
that its displayed reconstruction pullbackIso is a morphism in Mathlib's
independently packaged general geometric descent category. The predecessor's
exact coaction/overlap recovery and unique compatible affine morphisms remain
available, but that final category identification is not inferred from them.

Compatibility across different affine base charts, arbitrary-cover gluing,
rigidification gluing, Picard associated-sheaf identification, degree zero,
Jacobian representability and the full arithmetic theorem remain further work.

## Validation

Five new sources and45 byte-identical predecessor copies are bound. The copies
come from the41-source geometric-morphism packet and the actual nerve packet,
with four additional actual scheme nerve sources (the other producers overlap).
No previous source bytes are changed. Static hash/import/placeholder checks and
audit-history self-tests pass. No local Lean ran. Complete50-source hosted strict
replay, recursive axiom audit and independent acceptance remain pending.

## Revision r2: explicit defining upstream import

Run42579034823 at c2b05cf passed15 predecessor modules, including the scalar
composition and restricted coordinate repairs, then found Adjunction.toComonad
absent from AffineTripleOverlapMaps318's import closure. This revision adds
only the exact pinned Mathlib.CategoryTheory.Monad.Adjunction public import.
Forty-nine source files remain byte-identical, and the revised source has no
mathematical body change. The original50-source packet is preserved, and exact
producer failure evidence is retained here. Full hosted replay/audit remains
pending; no local Lean ran.
