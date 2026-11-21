# Independent review: constant-conductor marked receiver and the literal prime-29 gate

**Verdict:** PASS, in the paper and exact finite replay scope below (2026-11-21).

## Exact inputs

- Author manifest: `facf90df7aa487d01cbe9d0813193715dc051c3e4f190d5a65380cca5bb3d621`.
- `CONSTANT-15-MARK-AND-UNIFORM-29-SOURCE-GATE.md`: `2a850c80dcbc7bfd313cf140a274e794bd07d1777bbd6ab870f5b1e566993274`.
- `replay_constant15.py`: `bd7885b56a7501c09d68772c53cee100dd4226c108f745557fec8c75f07206b9`.
- `EXACT-CONSTANT15-CONTROLS.json`: `b58daeef346cd802cb95c489a6872eea3e6d5ab6fd7cc33b9d14c78e3b7cb33b`.
- Author checksum list: `9c5a7b2f8a0fde87cd059a76725696ea5066ddd65c8955634432396ae37d1e17`.

From the author packet, `sha256sum -c SHA256SUMS` and `python3 -B replay_constant15.py | cmp - EXACT-CONSTANT15-CONTROLS.json` passed independently.

## Mathematical checks

1. The ratio of the two known first-mark twists is the receiver equation with the common quadratic factor canceled on the legitimate open. Direct substitution gives the two cubic point equations of `NormalizedPolePoints318.PointPair` with the same fixed pole, first abscissa B, second abscissa B times the square of the nonzero scale, and second twist exactly the first twist times B²δ₀. Both ordinate factors are nonzero on the allowed real ranges. This is a sufficient single receiver for the literal interface, not an equivalence with every way of realizing a PointPair.
2. The change of variables identifies a rational point away from the excluded boundary with the specified scalar x-Kummer class on the twist with roots 0,d,81d. The torsion classes do not supply the mark: the greatest real root is the only root that could be halved, and its difference with zero is nonsquare; odd torsion is killed by the exponent-two Kummer quotient. The conductor-15 base model of the 2-isogenous curve and its local quadratic-twist signs give global root number +1 for the literal a=0 class, not a rank inference. For the local twist input I checked [Bisatt, Theorem 1.7](https://research-information.bris.ac.uk/ws/files/198735914/explicit_root_numbers.pdf).
3. The two-conic model gives smooth boundary seeds whenever either required class is square locally, including the actual dyadic and triadic guards and the supports of β and θ. At remaining primes at least 7, reduction of the four distinct branch points gives the smooth genus-one argument. At 5, primitive reduction explicitly excludes the both-nonsquare unit case; the literal a=0 case is in the soluble branch because θ is square there. The additional older strict odd-twist requirement at 2 fails for this receiver and is not part of the literal PointPair contract.
4. The replay follows all 20 states of the fixed original cyclic source, not one successful index. The finite values cannot cancel the prescribed norm factor at 29; the nonsquare −R prevents cancellation in the quadratic sum. The normalizer has depth one, so the actual c₀ has strictly negative odd valuation and δ₀ has nonsquare leading unit. This excludes the shortcut e=1 uniformly for the same cyclic source. In every local solution of the full receiver at 29 the valuation of e instead must be the exact positive odd integer −v₂₉(c₀); this is not an exclusion of all local or global solutions.

No rational point, marked lift, or rank is established for the actual receiver. The positive replay fixture is an unlinked numerical pole. No Lean elaboration or end-to-end quartic implication is certified here.

*Signed: independent proof reviewer, 2026-11-21.*
