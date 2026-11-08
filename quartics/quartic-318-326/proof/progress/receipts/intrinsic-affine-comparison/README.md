# Intrinsic affine differential comparison

This isolated proof packet constructs the canonical comparison between the intrinsic relative differential sheaf on an actual affine scheme and the tilde sheaf of its algebraic Kähler module. It is a continuation of `restarted-intrinsic-differentials`, without edits to the shared repository or upstream packets.

## Mathematical construction

- `LocalizationDerivation318` proves existence and uniqueness of extension of a derivation from a ring to any localization, with values in any module over that localization. The proof uses square-zero extensions and denominator cancellation. There is no domain, reducedness, rank, or field hypothesis.
- `AffineDerivationDetermination318` proves that a genuine sheaf-valued derivation on Spec S is determined by its actual global sections. It applies localization uniqueness on the actual basic-open basis and sheaf separation.
- `AffineIntrinsicComparison318` defines the canonical tilde-Kähler to intrinsic-Omega map via the genuine tilde/global-section adjunction, proves its global differential normalization, and proves it is an epimorphism.
- `DerivationFromBasis318` proves that additive sheaf maps satisfying the derivation laws on the affine basis satisfy those laws on every open.
- `AffineBasicDerivation318` extends global derivations to the actual basic-open regular-function rings and proves restriction compatibility by localization uniqueness.
- `AffineDerivationExtension318` uses the genuine sheaf basis-extension equivalence to extend every global derivation to every open. Extension and global evaluation are inverse.
- `AffineIntrinsicIso318` constructs the inverse to the canonical affine comparison. Thus the affine comparison is unconditionally an actual sheaf isomorphism, normalized on universal differentials.
- `AffineIntrinsicFrames318` matches the affine coefficients with the exact Spec structure morphism, preserves the original algebra instance, and transfers proved algebraic frames to intrinsic differential sheaves on the actual x, finite, and infinity charts.
- `HodgeInvertibilityCriterion318` proves a precise criterion for invertibility of the existing canonical Hodge-to-identity map: actual regular-function descent and an actual intrinsic differential frame. It uses the adjunction-unit identity and naturality, not a separately selected comparison morphism.

## Remaining boundary

The affine comparison is proved, not assumed. The packet does not itself identify the intrinsic global Omega on the complete glued family with its previously constructed invariant structure line. That requires compatibility of intrinsic Omega with actual open restriction and gluing of the normalized local identifications. The criterion for Hodge-map invertibility has explicit geometric hypotheses; it is not an unconditional family theorem here. A separate lane is proving actual regular-function descent from properness and integrality.

No compact modular/PEL source, canonical or bicanonical identification, analytic or metric comparison, final global-source realization, or unconditional arithmetic soundness theorem is asserted.

## Verification

`bash verify.sh` serializes the full strict replay under the shared heavy-compilation lock. It rebuilds all modules with `debug.skipKernelTC=false`, then recursively audits every declaration, including private and generated declarations. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted. Run `python3 create-receipt.py` after a successful replay to freeze hashes and the audit count.

No new copied Mathlib source is introduced. The preceding intrinsic packet documents its pinned source-cache substitutions; repository integration may use canonical pinned Mathlib imports as already arranged by the checkpoint integrator.
