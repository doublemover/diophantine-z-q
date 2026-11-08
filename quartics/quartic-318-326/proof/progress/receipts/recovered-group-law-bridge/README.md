# Both-infinity chart joins for relative Weierstrass addition

This packet continues the actual relative short-Weierstrass group-law construction over a commutative coefficient ring. It does not replace the curve by field points and uses no reducedness or density assumption.

## Scope

- Exact polynomial compatibility between the regular both-infinity Vieta formula and the mixed-input formula, followed by actual output Scheme-morphism equality under literal input transitions.
- A concrete principal-open overlap in the infinity-times-infinity product, with its actual finite extraction, output equality, input equality, and open immersion.
- Symmetry of the regular both-infinity output on the reversed-input overlap, including equal inputs and nilpotent directions.
- Exact finite-coordinate norm and trace identities, and recovery of the finite tangent divided difference from the original infinity divided difference.
- Homogeneous compatibility with both the ordinary-chord and tangent families, without canceling the input difference or output ordinate.
- Actual Scheme-morphism agreement with all four finite-input local addition maps.

The local polynomial and regular-chart comparison theorems do not introduce a field hypothesis or discriminant-unit assumption. Statements over a common coefficient algebra retain their explicit literal input-coordinate transition hypotheses; the concrete mixed overlap discharges these for its specified principal localization.

## Exact boundary

The cover-level comparison with the glued finite-input law remains unfinished: its draft hits an elaboration limit in the image-span specialization. This packet does not glue the three opens of the whole infinity-times-infinity input product. It does not establish all four global input-chart joins, construct a multiplication on the full completed relative curve, or prove global associativity, identity, inverse, or commutativity. No relative multiplication-by-N morphism or primitive torsion scheme is claimed. The remaining categorical gluing and group axioms must still be proved.

## Verification

Run `bash run.sh`. The script holds the single shared compile lock, rebuilds the listed modules sequentially with Lean 4.35.0, one thread, a 6 GiB cap, and `debug.skipKernelTC=false`, then recursively audits every declaration in those modules, including private declarations. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. This is a rebuild of the packet and recursive audit of its proof dependencies, not a fresh rebuild of all upstream sources.

The concrete localization is constructed generically before substitution of the curve coordinate ring. This avoids the kernel's exponential instance-comparison expansion without disabling kernel checking or introducing a proof axiom.
