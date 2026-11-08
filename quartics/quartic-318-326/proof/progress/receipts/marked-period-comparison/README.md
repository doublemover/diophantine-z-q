# Actual point-level period and diamond comparison

Strict Lean 4.35 replay and exhaustive recursive axiom audit: PASS, 16 declarations in two producer modules. Only propext, Classical.choice and Quot.sound occur.

This packet provides a concrete comparison step between the constructed analytic quotient and the intended point-level modular convention. It does not replace the missing algebraic or arithmetic comparison with an assumed identification.

- `MarkedPeriod318.standardPoint` is the actual complex elliptic point obtained by the already proved torsion parametrization from residue pair (0,1). Its literal period is 1/N, and its exact additive order is N.
- `label_stabilizer` proves that the genuine inverse-transpose residue transport fixes this marking exactly for matrices in the actual Gamma1(N) congruence subgroup.
- `point_stabilizer` proves the same equivalence for the actual additive elliptic-coordinate transport, not just formal residue labels.
- `quotient_eq_iff_marked_transport` identifies equality in the genuine analytic Gamma1 quotient with the existence of an actual integral modular period change preserving the canonical marked point.
- `MarkedDiamond318` identifies preservation of the H-orbit of the marking with the literal congruence condition c = 0 and a in H. It proves the equivalent conventional condition c = 0 and d in H by identifying the inverse diamond unit through ad-bc=1. It also proves equivalence with transport of the actual complex elliptic point into the same H-orbit of torsion labels.

## Exact remaining comparison

The existence quantified in the quotient theorem is an integral modular period transport. It is not a theorem that every algebraic isomorphism between complex elliptic curves arises from such a transport, nor that every complex elliptic curve has been parametrized by the constructed family. The H-orbit theorem does not build an analytic Gamma_H quotient or extend its maps across cusps.

The relative primitive N-torsion scheme and its actual equivariant faithfully flat splitting, the algebraic moduli universal property, the specific point-level rational-model identification, and the analytic/algebraic compactification comparison remain separate. Nothing here identifies an auxiliary elliptic modular model with the specified PEL/Shimura curve.

## Replay and provenance

Run `bash build-all.sh` while holding the common exclusive heavy-compile lock. Both producer modules and an exhaustive import-all recursive audit are rebuilt sequentially with `debug.skipKernelTC=false`. Public, private and generated declarations are checked; only propext, Classical.choice and Quot.sound are allowed axiom roots.

Imported predecessors use the pinned checked cache. This is not a full dependency-closure replay or an independent review. The receipt binds the exact sources, logs and predecessor receipts. Compiled artifacts are excluded from the frozen packet. No shared repository, manuscript, branch or PR was changed.
