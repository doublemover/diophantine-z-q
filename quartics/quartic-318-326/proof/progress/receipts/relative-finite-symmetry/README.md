# Actual relative finite-input commutativity

This packet proves exchange invariance of the actual four-chart finite-input Weierstrass addition law, over an arbitrary commutative coefficient ring with unit discriminant for the global finite law.

- Exact secant and numerator identities retain equal-input, tangent, inverse, and nilpotent directions.
- The tensor exchange map preserves the four actual local domains. The chord denominator and chord infinity numerator change sign; the tangent denominator and tangent infinity numerator are preserved.
- Actual local Scheme outputs are equal on every coefficient algebra after exchange.
- The four joins descend through the existing finite-input open cover to commutativity of the whole finite-coordinate addition morphism.
- The tensor exchange is identified with the categorical symmetry of the actual relative finite-input fiber product. Thus the last theorem is a Scheme-morphism equality on that fiber product, not a statement only about field points.

This does not construct multiplication on the entire completed relative curve or prove its global group axioms. It supplies the finite commutativity needed to join the two mixed-input charts.

Run `bash run.sh` for sequential bounded replay under the shared compile lock and the recursive declaration audit. Lean 4.35.0, one thread, 6 GiB cap, `debug.skipKernelTC=false`; allowed axioms are only `propext`, `Classical.choice`, and `Quot.sound`. Imported proof dependencies are recursively audited; this is not a fresh rebuild of every upstream source.
