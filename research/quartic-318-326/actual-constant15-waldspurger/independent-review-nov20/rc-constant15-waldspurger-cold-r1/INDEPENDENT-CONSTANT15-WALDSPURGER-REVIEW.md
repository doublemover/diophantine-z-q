# Independent review: a fixed-level Waldspurger test for the constant-15 receiver

**Verdict:** PASS for the exact coefficient formula and replay scope, 2026-11-21.

## Exact inputs

- Author manifest: `5a8ca5f5be2e2c2ceea915110002559637324d5f0654011a4c1e73be42aa91e3`.
- Paper: `38374b02240d1e31b8eefbf03c66b63b6b035fded686f913a604c7221b82ac4e`.
- Checker: `842fe4e3327b9678cedc8292cd2c8b94db6464093bf352f21b70adf76adcb1eb`.
- Replay JSON: `d127e973549a6ecacb8c36516c5adac979f8ac6955275ecc06fa03ae8f36150c`.
- Author checksum list: `f043603768c383fc76a61c6de81530f731914a691dc03e2fc5daf627f7b01409`.

I ran the original checksum list and independently byte-compared the standard-library replay against the archived JSON.

## Checks and limitations

1. The fixed weight-two form is the unique level-15 newform; the author uses the same isogeny class and same marked quadratic twist as in the receiver. In [Sirolli–Tornaría, Theorem 9.2](https://arxiv.org/pdf/2107.04483), the sign type is (−,−,+) at (3,5,∞). At 5 the level exponent is one and γ=ε=−, so a ramified discriminant is explicitly allowed. At 3, γ=− and ε=+, so the discriminant must have nonsquare unit class. Theorem B and Proposition 8.1 remove the auxiliary coprimality used only in the initial step of the proof; no unproved coprimality of the production discriminant with 23 is needed. The construction has its only type-II weight at 3, and level 180.
2. The modern construction identifies the older composite-level examples. [Pacetti–Tornaría, §3.2 and Table 4](https://mate.dm.uba.ar/~apacetti/papers/Compositelevels.pdf) give the exact prefactor for the signed ternary form and the extra factor 2 for the class ramified at 5. The substitution u=2x−z identifies the parity lattice without index error. I checked the two first-kind weight branches, the Legendre weight at 3, the even combined weight under negation, and the exact reduced equation after writing u=5U. For this lattice, changing isotropic vectors changes the first-kind weight only by a common sign: for distinct isotropic lines normalize the polar pairing, and use a Witt form xy+c z²; −c is square because the determinant of the original form is 15². Off the two lines the character of x therefore equals that of y, and on the lines the defining exceptional rule gives the same values. This fixes the potential choice seam beyond matching a finite table.
3. The 15 signed published coefficients agree exactly, as do the two separate numerical controls. The auxiliary character for −23 has sign + and conductor 15·23²; its independently bracketed classical central value is strictly positive. I checked the sign-aware Mellin sum, the exponential and π bounds, and the geometric bound for the discarded terms.
4. The formula tests the completed arithmetic obstruction only if the **actual** coefficient is evaluated and found nonzero. Then its central value is positive and the analytic-rank-zero theorem gives rank zero, excluding the nontorsion mark on this specific constant-conductor receiver. A zero coefficient by itself gives neither a rational point nor a rank result. This review does not supply the original coefficient, rule out the unrestricted PointPair, or certify any Lean build.

*Signed: independent proof reviewer, 2026-11-21.*
