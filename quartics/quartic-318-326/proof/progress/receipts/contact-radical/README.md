# Actual contact radicals to detector heights

This six-module supplement closes the arithmetic bridge from consumed positive odd rational contacts to the actual rational height bounds with exponents 49/104, 49/32 and 49/64. It does not assert the global geometric five-contact theorem or the local source-to-index divisibility producers as proved.

## Proved

- Literal primitive homogeneous forms [v,u,u-v,u-2401v,32u+343v], including infinity, and a genuine finite set of their odd prime factors.
- Exact exceptional set {2,3,5,7,11,13,17,37,41,73,109,359,439,2399,4801}. Its product is 11185621387570686764517810 < 2^84. Every remaining prime is at least 19 and avoids contactModulus, 17 and 41.
- Primewise p^k divisibility implies divisibility by the kth power of the entire actual radical, then the precise real-power bound for nonzero integer N.
- For detector t=a/b, the tuple (2a+b:a) is primitive and represents phi(t)=2+1/t. Its projective height is actual Mathlib height, and h(t)≤h(phi(t))+log 3 is proved exactly.
- Each good odd prime in this detector radical yields an actual source contact t-root(j) with positive odd integer additive valuation. The denominator and coefficient units are derived from coprimality and the exceptional set.
- Source contactPolynomial(t)≠0 gives nonvanishing of all five primitive forms.
- The complete geometric coefficient and additive 128 are absorbed into the literal height constant 2^5385.
- ConsumedContactHeight318.detector_height accepts the actual positive-odd-contact divisibility contract and concludes h(t)≤(2^5385+log 3)|N|^(49/(8k)). detector_high13 and detector_low4 give the two detector exponents.
- scalar_order8 uses the original rational point (beta.num:beta.den), with no phi or log 3, and concludes h(beta)≤2^5385|N|^(49/64).
- t=1 has actual empty good contact support/radical 1 and height 0, and beta=0 has height 0. The endpoint height lemmas need no local or geometric premise.

## Exact retained interfaces

ContactHeight318.FiveContact49Height is an explicit proposition parameter, not an axiom or a proved theorem. It states the 49/8 bound for actual primitive rational projective points, the literal forms and the actual radical. The metric/conductor/isogeny proof must supply it.

ConsumedContactHeight318.ContactDivisibility is the local upstream contract: each prime outside the exact exceptional set, each actual finite contact with positive odd order, divides N to exponent k. This packet proves the finite product/height consequence, not the source elliptic logarithm/index argument supplying that contract. Scalar source contact extraction is likewise a separate producer.

## Verification

Lean 4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. All six modules were compiled with debug.skipKernelTC=false, and ContactRadicalAudit318 recursively audited 71 declarations including private helpers and all their axiom dependencies. Only propext, Classical.choice and Quot.sound are allowed. No proof placeholders, custom axioms or native evaluation are used.

Replay with bash build-all.sh in the pinned workspace. run-one.sh lists the already-built source/height proof dependencies. This archive is a supplement, not a duplicate of those dependency packets. Binary outputs and experimental probes are excluded.
