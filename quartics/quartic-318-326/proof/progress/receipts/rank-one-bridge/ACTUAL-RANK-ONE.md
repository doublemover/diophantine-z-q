# Actual rank one and odd free index

`ActualGlobalRank318.odd_rank_one_data` proves the exact proposition `GlobalSaturationLogic318.OddRankOneData` for the actual elliptic curve over Q(sqrt(2)). There are no remaining rank, torsion, finite-generation, arithmetic, or height hypotheses in this final theorem.

## Derivation

1. The separately audited quotient packet proves finite generation of E(K). The quotient by the actual integer torsion submodule is therefore a finite free Z-module, by Mathlib's proved PID module theorem.
2. `ActualFreePart318` proves that the four displayed points O,T0,T1,T2 are distinct actual 2-torsion points. If the free quotient had two independent basis directions, lift those basis vectors to actual points. Their two binary coordinates and the four torsion points would produce sixteen distinct labels in the already proved ten-label quotient by doubling. Equality of labels forces the binary coordinates equal by integer parity. It then forces the torsion points equal because every torsion point is killed by two. Thus the free rank is at most one.
3. The independently proved infinite order of the actual point R shows its image in the free quotient is nonzero. The free rank is exactly one.
4. `ActualRankOne318` lifts a basis generator of that rank-one quotient to an actual point G. Every actual point is an integer multiple of G plus actual 2-torsion. The independently proved nondivisibility of R modulo 2-torsion supplies the odd integer coefficient of R.
5. `ActualGlobalRank318` discharges the torsion hypothesis using `GlobalTorsionOddIndex318.torsion_is_two_torsion` specialized to the constructed `ActualCanonicalHeight318.canonical_data`. That torsion theorem uses the checked small-height enumeration, not an assumed torsion-reduction injection.

## Verification

Run `bash run.sh`. All three modules are rebuilt with kernel typechecking enabled. `RankAudit318` recursively audits every declaration in the packet, accepting only propext, Classical.choice and Quot.sound. The receipt records exact source and log hashes and the immediate height/canonical-height dependencies.

This closes the rank-one/odd-index input. Final integration with the separately proved saturation and source-label theorems belongs to the height/source wrapper lane. No repository files were changed and no PR was opened.
