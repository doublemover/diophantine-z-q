# Unique descent of original affine geometric morphisms

This41-source draft extends the36-source geometric affine line reconstruction
with five new sources that descend actual covering sheaf morphisms and preserve
their exact composition laws. Thirty-two predecessor sources are copied byte-for-byte; four proof elaboration repairs are bound separately.

## New result

For a fixed faithfully flat R-algebra S, take two original line-sheaf overlap
data on the affine tensor-spectra nerve. Each datum consists of the original
line, an actual geometric overlap morphism and its geometric diagonal/triple
equations. Given an actual sheaf map between the covering lines whose original
overlap square commutes, there is exactly one sheaf map between the reconstructed
base lines making the original pullback square commute with the original
reconstruction comparisons.

The construction retains the actual global-section map, converts its geometric
overlap square to the exact original module-coaction square, applies the
faithfully flat equivalence's inverse functor, and takes tilde. The comparison
square follows from that same equivalence's actual counit naturality and the
original tilde pullback/counit naturality. Uniqueness uses actual faithfulness of
scalar extension derived from comonadicity and the full faithfulness of tilde.

Identity maps, compositions, actual inverse pairs and transition cocycles descend
exactly. This provides uniquely determined affine transition maps, rather than
independent abstract isomorphisms that might fail to glue.

## Source roles

- `OverlapMorphismCoaction318`: actual sheaf overlap square to actual original
  module square and coaction-compatible map.
- `GeometricAffineDescentData318`: original geometric data and compatible maps,
  derived coalgebra maps, inverse-equivalence module maps and their exact
  comparison square. The geometric datum is not defined as a coalgebra.
- `FaithfullyFlatTildeFaithful318`: actual scalar-extension faithfulness and
  actual scheme-pullback faithfulness on all affine tilde objects.
- `GeometricAffineDescendedMorphism318`: an actual descended sheaf map, its
  original pullback compatibility square, and existence and uniqueness.
- `GeometricAffineDescendedFunctor318`: exact identity/composition laws,
  descended inverse pairs and exact transition cocycles.

## Remaining boundary

The affine base ring and its faithfully flat algebra are fixed in these map
results. Compatibility of reconstruction across distinct affine base charts,
identification with an independently constructed general scheme fiber-product
nerve, and gluing over an arbitrary scheme cover remain further steps. This
packet does not claim a completed general geometric descent equivalence,
rigidification gluing, Picard representability or the full arithmetic theorem.

The predecessor's line existence and exact overlap recovery remain in scope
with their stated boundary: recovery uses the original geometric/coaction
correspondence; the general geometric descent-category comparison is separate.

## Validation

Five new sources,32 exact producer copies and4 explicitly repaired producers are source-bound, with exact
producer locations and hashes. Static hash/import/placeholder checks and
audit-history self-tests pass. No local Lean compilation ran. Hosted strict
checking of all41 sources, recursive axiom auditing and independent acceptance
are pending. No pending predecessor is promoted or relabeled as accepted.

## Exact hosted repairs folded into this superset

Run42577530786 at e3a0ead passed the first14 scalar/coassociativity producers
(including the previous scalar-composition repair), then found missing local
R-module instances in triple coordinate expressions. The coordinate source and
its two immediate tensor-formula consumers now use only canonical restriction
through algebraMap R S and its scalar tower. The tilde packet passed its global
section coherence source, then needed NatTrans.id_app explicitly reduced before
Category.comp_id in the finite mate proof. These four repairs preserve all
mathematical statements and actual maps. Exact logs/RESULTs are retained here;
committed predecessor packets, including the36-source packet, remain unchanged.
