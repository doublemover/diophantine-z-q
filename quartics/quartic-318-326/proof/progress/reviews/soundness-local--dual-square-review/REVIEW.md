# Independent dual-square review

Scope: the exact 11-module dual-square packet plus its recursive audit harness, copied from dual-square-bridge. Sources were compared byte-for-byte with the producer after rebuilding. The build used Lean 4.35.0, the existing pinned Mathlib cache, and debug.skipKernelTC=false.

Result: PASS. Independent full rebuild and recursive axiom audit checked 160 declarations across 11 modules. Every axiom root is propext, Classical.choice, or Quot.sound. The reviewed source hashes are in REVIEWED_SHA256SUMS; complete fresh output is in rebuild.log.

The substantive path was inspected: nearest-lattice rounding gives a strict Euclidean norm remainder in Z[sqrt 2]; the embedded ring is proved to have fraction field K; prime multiplicity valuations and reduced numerator/denominator arguments turn even values into a square times a unit. Totally positive units are squares using the actual Pell generator. The dual equation forces positivity in both real embeddings and even values at every actual ring prime. The exceptional prime delta=3-sqrt 2 is proved prime by its explicit F7 residue map; the anisotropic u^2+4 residue obstruction excludes valuation one. All remaining primes are handled without a split/inert prime-classification hypothesis, using v(2)=2v(sqrt 2). Zero numerator/denominator and finite-valuation requirements are explicitly discharged.

GlobalDualSquare318.dual_square_abscissa proves the exact existing DualSquareAbscissa assertion unconditionally. Its square_halving corollary invokes the previously proved explicit group-halving construction. No PID, unit classification, prime coverage, local solubility, rank, or sourceArithmetic premise is hidden in that conclusion. The separate canonical_R_positive lemma remains appropriately conditional on its explicit CanonicalData; this is not used to replace a global canonical-height construction.

This review does not claim the global rank/first descent/canonical-height or final source soundness theorem. The auxiliary split/inert signature modules were also read, but the unconditional square conclusion uses the stronger direct ring-prime argument.
