# Actual scheme fiber-product and tensor-spectrum Cech nerve

Three new sources identify the actual double/triple scheme fiber-product nerve
with the exact tensor-spectrum nerve used in geometric affine reconstruction.
The maps are explicit and preserve the whole diagram, not just object classes.

- `ActualAffineDoubleNerve318` uses the original pullbackSpecIso for the actual
  double fiber product. It retains both projections, the base map and the actual
  diagonal, which is the spectrum of tensor multiplication followed by the
  inverse same double comparison.
- `ActualAffineTripleMaps318` builds a map from the literal triple tensor
  spectrum into the actual adjacent-double fiber product, using the actual12
  and23 pair maps. Its inverse candidate is built using actual vertex0 and
  pair12 and the original outer pullbackSpecIso. All vertex formulas are proved.
- `ActualAffineTripleNerve318` proves these two actual maps are mutual inverses
  by the two original pullback universal properties. It proves preservation of
  all three pair maps, including the omitted02 edge corresponding to13 in the
  tensor-index convention.

The schemes, maps and equalities are exactly those of ActualOverlapDiagram318
and AffineCechRings318. All commutative rings and R-algebra structures are allowed;
no faithful flatness, reducedness or field assumption is needed for this diagram
identification.

The next step is transport of actual sheaf descent data and its equations
through these isomorphisms with canonical sheaf pullback comparisons. This
packet does not claim that transport, the general geometric descent-category
equivalence, arbitrary-cover gluing, Picard representability or the full
arithmetic theorem.

## Validation

Three new sources and five byte-identical producer copies are bound with exact
locations and hashes. Static source/import/placeholder checks and audit-history
self-tests pass. No local Lean compilation ran. Hosted strict checking of all
eight sources, recursive axiom auditing and independent acceptance are pending.
The original producer receipts do not constitute acceptance of this new join.
