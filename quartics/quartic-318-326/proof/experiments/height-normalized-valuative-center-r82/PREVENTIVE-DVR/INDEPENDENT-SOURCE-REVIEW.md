# Independent source review: DVR twist normalization repair

Verdict: narrowly justified proof-shape repair for future hosted checking; not a Lean acceptance result. No local Lean run.

SOURCE-APPLICATION SHA256 9e161d8b9115dd391f509ccc4b33d2a564bde837c64497e3abadeb3fd3cc38f8; all six bindings independently verified.
Before d565adbedae7af76700a270af774e1400fc3c7c1ca8e64d4a103d82acd63fab5.
After 8a73e62e8d0817576a8fcedc26cf4a62d3fb92a997c9a12b6b71490b34e435d4.
Own run43670426442/commit7cbf02dd9bed3447c5d46502ebeb4f4c7aa7221b receipt SHA02f2dab19a931d1f69639b9909c06c95a23a56e811a9d3fe1c9b86346f538e96 and exact failure log62379a0b964f2fab08d86c89ff8f4fdef8bc255f913c0960ca9b206ed57a9422 match the independently inspected collector.

The actual error occurs because congr 1 splits the differently associated products and leaves the unit factor as the left-hand conversion target; rewriting n there is impossible. The candidate isolates the intended POWER equality at explicit type K, using n=e+2*(n/2), native zpow_add with the already proved nonzero image of pi, zpow_mul and integer-to-natural powers. It then rewrites the full product and uses ring for associativity. This removes dependence on congr goal selection without replacing any mathematical input.

The integer n and n/2 retain negative valuation cases; e is still the actual nonnegative parity residue in Fin2. The unit and square multiplier are exactly those of the native DVR decomposition. No integrality of c, unit image of pi, new scalar tower, changed public statement, proof-only binder, resource setting or division in V is introduced. The normalize_four consumer remains byte-identical and transports all four actual coefficients.

All nine obligations are local to this normalization. Current observed status is exactly QuadraticFiniteDual full PASS2.671s, TensorFiniteDual full PASS1.970s, then this module FAIL1.920s: two of17 draft roots pass, one fails, fourteen are unreached; nineteen baseline dependencies reused. The new candidate is not checked by that receipt. Whole cofactor/finite-dual/geometric claims remain downstream. No source was propagated or active packet edited by this review.
