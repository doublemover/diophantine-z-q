# Constructing both fine level-33 family comparisons

For the original discriminant-210 quaternionic abelian surface, the two proofs construct the scheme adding the missing principal mark over `Spec Z[1/33]`. They start with the actual fine level-3 or level-11 family, not an independently postulated forgetful map or family isomorphism. The fixed generic object is the same polarized surface with its two complete markings; nothing is identified by coarse moduli alone.

| Starting family | Torsion used | Delete | Relative degree |
| --- | --- | --- | ---: |
| [Fine level 3](tame11/ACTUAL-33-LEVEL-AS-TWELVE-KERNEL-COMPLEMENT.md) | `A_3[11]`, regular left matrix module | twelve rank-one operator kernels | 13,200 |
| [Fine level 11](ramified3/ACTUAL-33-LEVEL-FROM-THE-RAMIFIED-THREE-FRAME.md) | `A_11[3]`, regular left module for the ramified quaternion order modulo 3 | one radical multiplication kernel | 72 |

In both cases a surviving point is the value at 1 of a full frame. The projectors [22] and [12] combine the two actual marks. Both constructions therefore represent the same full principal-level-33 problem. They give actual Cartesian universal-family squares preserving the identity and the fixed compatible principal polarization. Once either old integral section is given, normality extends its one prescribed generic section of the new finite scheme on the overlap. There is no level-3 extension at residue 3 or level-11 extension at residue 11.

The [full-frame locus argument](frame-scope/KEEP-ONLY-THE-ACTUAL-FULL-PRINCIPAL-FRAME-LOCUS.md) clarifies the classical input: it uses only the clopen isomorphism locus of the level marking in the genuine fine model and the designated full generic frame. It does not infer invertibility merely from the notation for an O-linear map, or assume the full locus is the whole of an ambiguously described model. [Yuan v2 §2.1](https://arxiv.org/html/2205.11334v2#S2.SS1) supplies the classical models and compatible polarization; [Buzzard §1, Definition 1.1](https://www.ma.ic.ac.uk/~buzzard/maths/research/papers/shimura.pdf#page=3) identifies the tame full-frame convention, not a representability theorem at the discriminant primes. The good relative torsion and division-order calculations are in the respective proofs; [Voight, Theorem 13.3.11](https://jvoight.github.io/quat-book.pdf) gives the local division-order structure. Over the overlap 3 is invertible **on the base** while still ramified **in the quaternion algebra**.

An [independent review](review/INDEPENDENT-ACTUAL-FULL33-FRAME-COMPLEMENTS-REVIEW.md) checked both proofs, the full-frame-locus scope, the pinned primary statements and the exact finite residue-ring replays.

## Exact replay

From this directory, using Python 3 standard library and a POSIX shell:

```sh
sha256sum -c SHA256SUMS
python3 tame11/check_twelve_generators.py | cmp - tame11/EXACT-TWELVE-KERNELS.json
python3 ramified3/check_ramified_three_frames.py | cmp - ramified3/EXACT-RAMIFIED-THREE-FRAMES.json
python3 context/check_original_fine_overlap.py | cmp - context/EXACT-FINE-OVERLAP-CONTROLS.json
```

These finite checks verify the exact residue-ring and CRT calculations, not moduli representability or the arithmetic height conclusion. The older [overlap note](context/THE-SAME-POINT-FINE-OVERLAP.md) and its replay are historical proof context; the downstream native owners referenced there are not part of this source packet.

The only Lean file here is a source-only algebraic proof of extension of a generic finite-algebra section over a normal domain. It was not built and does not implement PEL moduli or the Newton/KS comparison. The abelian surface in this packet is not the distinct modular Jacobian used elsewhere in the reverse argument.
