# Immutable source provenance

The proof, code, and replay files are copied exactly. The original working manifests (identified by their own SHA-256) were checked together with their dependencies before staging:

- The 12-kernel tame-11 construction: `628435039ed25557849fe34e06f8f631ab42278902768f0e5ed5eaea4e30e1e0`.
- The one-kernel ramified-3 construction: `041ad627d5529413d4c0a4901d12a1af5d60034b9f9e2cdaf8479ad76fbc4216`.
- The precise full-frame locus: `2383afef8ed5acb2ea713035d56dbd5ff2d4f3ab211e54c2b60f426bd2a7f7c0`.
- The prior selected-point CRT overlap: `3fc607785f974d4ad06af141f494229883371c4f8c0ea0cd6709768afb2d501c`.

The new root manifest uses only portable relative paths and has no workspace-relative donor references. The computations require no separately installed packages.
