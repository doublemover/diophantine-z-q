# RC62 r11: exact qualified phase XOR repair

R10 exact hosted run 44861626474: 57 of exact 62 selected owners compile, 1 owner produces a compiler error, 4 blocked, and 42 owners not selected. 858 declarations audited with no audit failure. Inventory SHA-256 95a30ee2821f5bc5e22473e03759d11bfecd01742f34b57cc1ef4a3c218cb4ee. Source commit 384e8211e0545043594de1d5dba185eca429c6b8.

Sole owner repaired: CTActualQuadraticHOne318.lean. Line 100 invokes `phase_mul` and exposes the root carry's qualified `CTQuadraticCarrySwapAlgebra318.xor`; existing `bit_xor` is about generic Bool.xor, so rewrite under semireducible transparency cannot match these heads. Introduce the private `bit_source_xor` for the literal qualified operation; all four Boolean inputs are decided. Use that lemma only in this proof. All prior signatures, chosen root, bit encoding, actual field and Galois action, scalar Kummer classes, quotient boundaries and finite-support statement remain literally unchanged. No other Lean source/import delta: 103 peers byte-exact (including the presently unselected 104-owner terminal).

First target remains CTActualGloballyFiniteIsogenySelmer318, same ordered 62-source closure, no project baseline. No theorem on parity of Selmer corank, Mordell–Weil, or arithmetic Cassels–Tate. Source-only; no local Lean, remote write, or hosted run from this revision.
