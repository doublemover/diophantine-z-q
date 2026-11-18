# Arithmetic regular models for all 256 ordered dyadic twist types

**Result at paper/source level.** Let b=(0,32,76832,−343) and let each qᵢ be a nonzero rational number. The normalization X_q of the projective parameter line over Z in Q(T)(r₀,r₁,r₂,r₃), rᵢ²=qᵢ(T−bᵢ), has an explicitly described proper birational modification, flat and proper over Z, whose total space is regular. Its generic function field and original parameter map are preserved. The proof is by the earlier odd-prime models and the dyadic constructions assigned to the rows below. Regularity of the total space does **not** imply smooth or reduced arithmetic special fibres, minimality, semistability, an identified Néron lattice, rank, or the main 318/326 Diophantine result. These papers and finite arithmetic checks are **not** a kernel-verified theorem or an executed general-purpose resolution program.

## Select a proof

1. For each i, put nᵢ=v₂(qᵢ), uᵢ=2⁻ⁿⁱqᵢ. Take εᵢ=+1 if uᵢ≡1 mod4, or −1 if uᵢ≡3 mod4. The chosen representative is εᵢ·2^(nᵢ mod 2). Removing a square from the ratio leaves a unit 1 mod4: adjoining its square root is unramified or split near 2, via the integral quadratic for (1+√unit)/2. The cited sign/étale comparisons explain why geometric regularity and the specified modifications descend. No equality of rational exceptional-point splitting under every twist is asserted.
2. Encode (1,−1,2,−2) as (0,1,2,3); the two-hex-digit mask is 64d₀+16d₁+4d₂+d₃, q₀ first. For example q=(1,−1,2,−2) has mask 1b. The [256-row table](cover.json) lists the representative and the single *primary* terminal proof selector.
3. Look up that key in the [proof map](proof-map.json). Its path is relative to this folder and its SHA-256 binds the exact mathematical source. The support list is navigation, not a proof-assistant import graph; follow the paper's local comparisons and preceding stages. For odd primes use [the arithmetic open away from 2](../ramified-three-twists/RAMIFIED-THREE.md); [sign and étale descent](../sign-unramified-twists/SIGN-DESCENT.md) is common background.

| Disjoint partition on the original ordered representatives | Rows |
|---|---:|
| First three identical (any fourth) | 16 |
| First three odd and mixed, fourth odd | 12 |
| Equal first-three valuation parity but mixed signs; fourth even | 24 |
| Mixed first-three valuation parity, fourth even | 96 |
| Remaining fourth +1: mixed first-three parity, or all three even with mixed signs | 54 |
| Fourth −1, first three all even with mixed signs | 6 |
| Fourth −1, mixed first-three parity, majority-parity signs equal | 24 |
| Fourth −1, mixed first-three parity, majority-parity signs opposite | 24 |
| **Total** | **256** |

A selector is not an independent arithmetic construction for each mask. Several rows intentionally use one parametric argument; multiple earlier papers can apply to a row, but this index chooses exactly one primary terminal proof. A transformed chart is selected only after the actual signed rational Möbius coefficient update, and the nonintegral double/quarter parameter markings use their explicit chart comparisons. The original generic degree remains 16; the three-root models are intermediate étale chart calculations.

Run `python3 check_cover.py` for the finite enumeration and class-count checks. In the populated repository run `python3 check_cover.py --verify-sources` also to recompute every referenced source digest. This checks enumeration and identity of the papers, not their mathematical content or any Lean declaration.
