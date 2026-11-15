# Independent bounded current source review

Verdict: suitable for a scoped hosted repair experiment. Source/API/application review only; no local Lean run and no kernel acceptance.

Manifest: ae8e37f409a1da572e45a449d56d6da982beeefbffc923ba2b319f905fe6dda6; 18 exact bindings independently verified.
APPLICATION.json: 3aef630f87ce4ad6c0e6a0f2c5454600683bde3674e9fd9d76eb3832f892ea8f.
before/PELPositiveNormPeriodMap318.lean: 7ddfc7b7a5cd968116c22322bd81ff2e5d92d6ec69e82c8fc91550ad0c52fe10.
after/PELPositiveNormPeriodMap318.lean: 35a154fffbcbb9a5b82f6aab3b802d9e5d66fad33de4bbebd55bc8f5b04292ee.

Read the complete source diff, own trace25 failure, native surfaceCharts/descended_linear_between, and the existing UnitBiholomorph proof-local pattern. The two invalid section-local DiscreteTopology instances have proof-only hTau/hn arguments not inferable from their result classes. The candidate instead installs exactly the same derived discrete-period proofs inside originalMap_holomorphic, where both original positivity witnesses are available. The native surfaceCharts definition uses these same constructed proofs, so the chart selection is not replaced. Existing theorem/definition telescopes remain; anonymous instance scope deliberately changes. The actual map still goes from translated original surface onto the original surface for arbitrary positive-norm order elements, including nonunits. No inverse lattice equality or fixed-polarization isomorphism is asserted; exact reduced-norm multiplier and full vector/point coverage remain. Own trace25 has95 successes then PositiveNormPeriodMap FAIL2.019s; character and other copies require their own receipt/classification. All nine obligations retain this boundary.

All statements about future compilation remain unverified. Preserve the own failed predecessor evidence and unchanged earlier snapshots.
