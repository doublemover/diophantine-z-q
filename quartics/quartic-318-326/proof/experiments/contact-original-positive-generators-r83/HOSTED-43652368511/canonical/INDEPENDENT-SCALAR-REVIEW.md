# Independent scalar local-squares source/current-contract review

Date: 2026-11-14. Candidate ScalarLocalSquares318 SHA256c90edeea368ad0532c5e7729115511794d72805eac8e0e9f9d6c6305f14905cd; before SHA256ed729af8fd8c43dea9276d68eb4729b5b3dade88f807b42e37a9477698c77dfa; SCALAR-APPLICATION.md SHA256a171ab6574bc5cf9c3dd4aa6386d43dd3e8b47630cbeaf4b3448922a79e00dc0. All six source/evidence bindings recompute. No local Lean/Lake.

Read exact diff and authentic run43652368511 error log, all nine obligations and pinned PadicInt.norm_p declaration. The observed generic Hensel application fails at the representation of2 as1+1 inside a norm. The candidate separately proves F.aeval x=x²-v and F.derivative.aeval u=2u before forming the inequality, then uses the unchanged near-square hypothesis. This is the same polynomial, derivative threshold and actual Hensel witness, not an assumed square root or weakened inequality.

The three specializations retain all integer k, primes2/3/17 and shapes1+8k,1+3k,8+17k. Typed norms instantiate the native norm_p theorem at each literal prime with Nat.cast_ofNat, matching the numeral carrier in the actual goal. The p17 derivative is explicitly normalized2*5=10 and its norm remains1. The p2 estimate retains the cubic prime power8 against the square derivative threshold; no odd-prime shortcut is used. Integral-to-rational p-adic maps and all downstream pole/multiplier statements are unchanged.

No theorem statement, quantifier, local-squareness assumption, coefficient, nonzero condition, import or resource option changes. The native norm facts justify the source-level arithmetic; exact simp/rw/instance elaboration is still unobserved. The current SmallPrimePreparation module really exited0 before this new frontier, but that does not validate the rest of the arithmetic packet or this successor.

Disposition: PASS for isolated source and nine-obligation contract. Future descent/weighted successors require exact-copy propagation with their own immediate predecessor intake/results, independent current packet review and hosted strict/audit results. No full arithmetic solution or accepted-snapshot promotion is established.
