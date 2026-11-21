# Independent review: divisibility by eight of the literal constant-15 coefficient

**Verdict:** PASS for the stated uniform congruence (2026-11-21), not for evaluating the coefficient.

## Exact inputs

- Author checksum list: `31e7a8d1d0c349dca509cd3aad02987ec493136b755e52d05b1b8ab2e057318b`.
- Paper: `9d3de8e2ea40d282d429da4249f69a3bca7c5600ec97275ee9f25040e1b95d2c`.
- C++ checker: `758917a6b4c828b9d61c3f3daf6b02e5f73c434398e968749b1c4c3a609a38da`.
- Exact stdout: `6ff396c1c9a8a472d061e34898b720d3dd8a062060cb435d2a3100dde00edbdc`.

I verified the author checksum list, rebuilt the standalone C++17 computation and compared its complete output byte for byte. Independently I also enumerated every nonzero isotropic triple modulo 23, checking both fallback branches, all sign changes used in the orbits and absence of zero weight, and recomputed the three decisive quadratic characters.

## Checks and conclusion

1. For the exact fixed β, the norm axes and the two diagonals cannot occur: their binary forms are inert at the odd-depth primes 11 and 661 respectively. The nonsquare β unit at 23 implies even valuation for δ₀=1−βc₀², so 23 does not divide θ, and the vector at the weight prime cannot reduce to zero. The four signs on y,z preserve the actual weight; reducing the quotient modulo 2 makes the odd-u,z sector a fixed-point-free swap, without asserting signed swap cancellation.
2. In the even-u,z sector the precise remaining equation is 16 times the norm in the full integers of Q(√−15), plus 15y², with y positive odd. Its restriction at 11 is a nonresidue and removes both binary norm axes. Thus the integral one-orbit series B⁻ is exactly a quarter of the norm-nonresidue series. The two coefficient filters are finite rational translates; the exact conjugation permutation is j↦j d₀² modulo 11 and preserves the Legendre weighting and the character modulo 15.
3. The weight-two form is genuinely holomorphic with integral coefficients at infinity, at level 29040 and trivial character. One way to check its theta multiplier is to view each product of two unary theta functions as an ordinary binary theta for x²+15y² or x²+60y², of levels 60 and 240. Their characters agree on the common level, and their half difference times the scaled B⁻ gives the trivial character. Classical [Sturm congruence](https://doi.org/10.1007/BFb0072985) applies to this integral-weight form also modulo 2 at this even level.
4. The independent replay checked every coefficient through the inclusive Sturm bound 12672 of T₂₃U₅U₁₁ applied to that form, with identically zero constant term. The exact live-prefix diagnostics were nonzero on the input and at T₁₇. At index d/55, the lower-index T₂₃ term is absent because 23 does not divide d; the extracted coefficient is exactly the required index 23d. This proves c₋₂₃(βθ)≡0 mod 8 uniformly for the literal fixed-β Ready profiles, without enumerating that production coefficient or factoring unseen θ.

The normalized c₋₂₃/4 cannot be odd on these profiles. This does not determine c₋₂₃ as an integer, give vanishing or nonvanishing, bound rank, or produce or exclude a rational PointPair.

*Signed: independent proof reviewer, 2026-11-21.*
