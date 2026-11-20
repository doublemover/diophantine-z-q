# Independent exact review: direct level-48 conductor-four trace controls

Parent manifest SHA-256 `ff551fc90d1ad1b0b5d8f9ce8e1bb2b0934df9ef156679e4c11342a48fad60fd`.
Parent paper SHA-256 `d51442309aefd654187f1dd9d66c6513746666642bdba74030f7521c1e507318`.
Every parent manifest entry verified. The full chosen trace of 24 records matched byte-for-byte; each longer full row digest matched its compact frozen record.

The local choice at 2 is a literal cyclic line in the source basis `(1,4ω)`, with the source and target both of conductor 4. The four allowable eigenvalues give four different stable local types, not four weights to put on a trace. The chosen local root fixes one of these types, the marked line at 3 fixes the eigenvalue 1, and the selected residue-field embedding at 53 fixes one of the two conjugate phases. The tangent calculation for `(1,ω,γ,ωγ)` uses `J²=−3` and `dγ=J/3`, giving the stated coefficient `(3b+2c−g)/(3e)`. For `j=0`, no order-three geometric automorphism fixes a cyclic 16 mark, already by its action on the mod-2 line; choosing the simultaneous mark orbit representative therefore introduces no factor of three. Chart multiplicities from different actual CM classes remain in the sum.

[Cornut–Jetchev, Theorem 3.1, Corollary 3.2 and §3.6](https://webusers.imj-prg.fr/~christophe.cornut/papers/liftings.pdf) uses the fine conductor pair, here `(4,4)`; its coarse-conductor shortcut does not apply because 2 divides the level. At the sole reduction prime 53 the conductor and level valuations are all zero so the lift multiplicity is one. Restricting the away-from-53 marked local types and the residue embedding at 53 gives the one intended class-group orbit, of size 6h(K), not the other dyadic types or its conjugate phase.

The independent replay uses the separate frozen low-level chart source and weighted projective operations in the short model after translating x, rather than the author's affine secants. It verifies every order-13 projected row, independently sums all raw points, applies [224] after the full sum, divides by two ONLY on the order-13 subgroup by multiplying by 7, and makes the actual square-root twist conversion. The check reproduces:

| Positive d | One oriented orbit | Ring coefficient | Hilbert coefficient | Hilbert projection on E_d over F_53 |
|---:|---:|---:|---:|---|
| 323 | 24 | 9 | 11 | (42,11) |
| 132107 | 720 | 1 | 7 | (24,31) |
| 1139 | 96 | 11 | 12 | (11,46) |
| 465851 | 1248 | 7 | 10 | (44,51) |

The ordinary Hilbert trace here is the full trace, not an odd-suborbit sum: the earlier exact equality is [2] times that trace equals the ring-class trace. Good reduction at 37 has quadratic-residue-field count 32·44 prime to 13, excluding 13-torsion over the relevant quadratic fields. Thus these nonzero projected residues certify full-trace nontorsion for both substitute-scalar pairs. The common surrogate is β=17 and θ=409; no production scalar, fully completed production prime, or actual paired production trace follows.

To rerun the independent group check, use the parent enumerator **without** `--compact` to generate four files named `323.json`, `132107.json`, `1139.json`, and `465851.json` in one directory. Run `python -B check_projective_group.py DIRECTORY LOW-48-SUPERSINGULAR-F53.json`; the second input is hash-checked. Compare with `EXACT-REPLAY.txt`.

Cold review: Vesper, independent review lane.
