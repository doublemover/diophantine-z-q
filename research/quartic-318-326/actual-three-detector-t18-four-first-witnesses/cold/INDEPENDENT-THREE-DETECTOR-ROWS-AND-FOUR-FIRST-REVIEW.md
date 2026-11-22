# Independent review: one fixed construction for all four first witnesses

**PASS for the exact three-detector proof and its coexistence with the already checked scalar first witness at the same prepared index.**

| Bytes | SHA-256 |
|---|---|
| Three-detector author checksum list | 66bd21760d372a011f524490ee908df2a67b64ab6a7b8015c3db024bbed6706f |
| THREE-ORIGINAL-READY-DETECTORS-T18-NATIVE-ROWS.md | 2c0cbdc73db768e402b9c52ac7ca01983ed24118cbf741e23cb26e16fc9ccdba |
| Independent raw row replay | 84ed59ba17f0fb9dd9ddd370a8a3019b39aa9f87097d33bfd137dfc36d7a3f3c |
| Exact replay output | 16b1813eac1230ff162b206fedb91d1f332b87816d73732c32c8e04e2ad72fb2 |

I verified all five original native source hashes named in the paper, including the exact raw polynomial definitions and actual certificate fill. The attached standard-library replay compares every one of the 15 original polynomials over the rationals against its literal named slots and checks the three actual fill blocks. The two first-side rows for each detector are 152 and 154, 205 and 207, and 258 and 260. The fourth equation in every block indeed gives the negative product divided by three as the auxiliary coordinate; no changed polynomial or second-side value enters the first equations.

On a genuine key, each detector β is the positive squarefree integer 17 times the denominator prime times its five distinct contact primes, none equal to 17. The signed nonzero ρ is the literal stored fold's square factor with the stated clearing; its sign only selects a permitted ordinate. With the same normalization parameter t* = 18, I checked the exact first point, positive range 0 < T < B, ordered class ([B], 1), and both directions of the raw-to-affine companion transformation preserving δ = 1 − b/17. The raw ABI requires the scale to be nonzero, not the second ordinate. In the companion chart, w and its corresponding certificate and point ordinates may be zero. The Ready depths of B/289 are at least 3, 1 and 1 at 2, 3 and 17; the remaining local argument uses denominator parity on the fixed squarefree support and the good-reduction unit Kummer image at other nonsquare-unit places. These verify local admissions, not global companions.

The uniform scalar first proof is exactly checksum list e4f4c4f4462c7b50d3f66ec358ab35292e58087dba920650884c03be06aa7eed and paper 3aa0002833e43d578c82c8cd37d0cac3eb8f33f98156296374b5a13326c9cd94. Its first witness at the literal scalar slot 314 coexists with the detector first witnesses at slots 190, 241 and 292 on the same actual prepared h, key, labels and anchor. The four native T values need not agree. The existing complete-at-index interface applies only after receiving all four separate second witnesses at that same source; the original guards, non-pole rows and anchor remain in force.

No new common index, key, numerical points, global companion, rank, selected class or solution of the original system is asserted. No simultaneous preparation for arbitrary inputs is inferred here. The evidence is mathematical and exact raw polynomial replay, not a new native Lean theorem.

Signed: independent original-quartic reviewer, 2026-11-22.
