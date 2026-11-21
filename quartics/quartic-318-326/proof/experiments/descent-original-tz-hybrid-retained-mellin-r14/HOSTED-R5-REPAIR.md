# Exact TZ mean replay r6: two directly diagnosed proof owners

Predecessor intake 92d9d91634c3d869d5d194510fbc2d2b40a83c4c113af77e5477a971559a9299.
Exact observed run 44858398765: 33/39 compiled, 492 declarations
audited, 2 direct errors, 4 blocked, 91 unselected. Raw log and source
hash checked for each changed owner. Other 128 Lean files byte-identical,
same module import-name sets, same selected 39 order. No Lean or GitHub
operation by author.

- HybridGrid: move dependent `Fin` equalities to Nat-valued projection
  before applying congruence to the two inverse-index equalities.
  Normalize exactly the stuck `True` and `false = true` branches; write
  the actual (2M+1) width explicitly before the closed Nat inequality.
- IntegerGridMarker: identify evaluation of the zero coefficient
  function, instantiate the support-map inclusion over the exact
  `ZMod p`, and load the existing probability body for its proof.
  Split the integer divisibility condition once per original signed
  sample, transporting it in both directions across `residue_root`.
  No count or normalized denominator changes.

This is a source-only exact diagnostic successor.
