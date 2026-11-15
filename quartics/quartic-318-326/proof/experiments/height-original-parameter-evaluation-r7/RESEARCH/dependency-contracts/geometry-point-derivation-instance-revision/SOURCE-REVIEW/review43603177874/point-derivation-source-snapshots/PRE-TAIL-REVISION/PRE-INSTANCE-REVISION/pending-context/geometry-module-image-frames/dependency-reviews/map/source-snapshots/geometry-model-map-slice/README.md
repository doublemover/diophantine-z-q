# Original model frames to per-point metric sections

Status: isolated source candidate, independent review and hosted Lean validation pending. No active packet, source frontier, build budget, workflow or acceptance path is changed.

## What is implemented

1. A free rank-one frame of a **specified embedded** finite-place lattice yields its nonzero field generator. The principal lattice of that generator is proved equal to the supplied submodule. Its generator norm is independent of the chosen free frame.
2. A supplied surjective linear comparison between embedded lattices, with generic formula literally multiplication by the scalar, yields equality of the actual image submodule. The invertible-comparison specialization is used with scalar 210.
3. At excluded places, the original model generators are extracted from those supplied model frames, without consulting any Hodge metric or desired degree. The assembled lattice is proved equal to the supplied bad-place submodule; all previously constructed good-place lattices remain unchanged.
4. Supplied normalized comparisons at **every finite place** yield the current `LocalKSImages` proposition, then the existing original-section `MetricSections` constructor. The field, original section evaluations, coordinate 32u/v, normalization 210 and all local domains are retained.

This is a map-to-image/metric bridge, not construction of the missing models or a global KS theorem. In particular the normalized local map from canonical lattice to Hodge-product lattice is not silently identified with the native global KS morphism before its necessary frame normalization.

## Inputs still required

- A model lattice embedded in the original point field at each excluded place, a free integral frame, and membership of both unchanged original sections. These are still **assumptions**, not outputs of a bad-prime model construction.
- The actual Hodge determinant metric of the chosen surface, its finite generators and degree identification. The Hodge metric is never defined from the canonical metric by square roots or by the desired equality.
- Invertible normalized local comparison maps on every finite place with scalar formula 210. Their existence and identification with the actual global KS construction remain open inputs. No good-place or bad-place local map is produced here.
- The archimedean isometry and original section bounds.
- The actual CM/non-CM branch input records and their per-point production. The section field remains distinct from isogeny/averaging/model fields.

No `GeometricRealization`, final height inequality, numerical KS degree identity or all-place image equality is assumed by the new bridge. However the local comparison input is substantial: no claim is made that it is easier than the unconstructed geometric comparison. Conditional consequences do not prove global realization.

## Provenance and validation

Base: `2b151fc62f5872fd569489336d35f536d4cae0a4`. The exact original lattice dependency closure is the published r16 packet, whose hosted failure is still `IntegralOriginalCommonRestriction318`. All new downstream source remains uncompiled. The existing full-module successes of GlobalComparison/BranchCoefficients/InfinityCoefficients do not validate these new modules.

`PROVENANCE.json` pins all inspected repository producer/consumer/history sources. `PRODUCER-AUDIT.md` distinguishes actual constructions from assumptions and historical classical claims. `APPLICATION.json` records nine explicit obligations. No prior acceptance is copied as acceptance of this new route.
