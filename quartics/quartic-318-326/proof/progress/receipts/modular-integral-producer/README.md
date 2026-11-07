# Actual integral modular cover

`INTEGRAL-COVER-PRODUCER.md` constructs the actual finite-étale point-level cover on the open j-line and identifies its normalization after every number-ring extension. The result is the genuine vertical-support statement p|6N needed by the finite-divisor proof, not a conditional scalar inequality.

`OpenJModel318.lean` supplies the literal integral elliptic model on Z[j,1/(6N·j·(j−1728))], not just an equation over a field. It kernel-checks all inverted units, Δ=1728²j²/(j−1728)³, the ellipticity instance, exact j-invariant, and arbitrary ring base change. Twelve theorem/instance roots are checked.

Run `./build.sh` for a fresh strict-kernel rebuild and recursive all-declaration axiom audit. The permitted roots are propext, Classical.choice and Quot.sound only. `receipt.json` records the exact counts, scope and hashes. The scheme-theoretic torsion, quotient and normalization construction is the separate mathematical proof, not a Lean AG formalization. No resolution/intersection or full FiveContact49Height closure is claimed here.
