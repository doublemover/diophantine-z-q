# Pinned third-party source and license

The proof adapters import two modules of Shawn Krisman's Apache-2.0 Lean project [waldschmidt-subgroup-theorem](https://github.com/telaviv/waldschmidt-subgroup-theorem/tree/e116a28c34810a802868965d00d2ae986fa627e7), pinned to commit e116a28c34810a802868965d00d2ae986fa627e7. The original file notices read “Copyright (c) 2026. All rights reserved. Released under Apache 2.0 license.” The original headers are preserved byte for byte. A separate prominent modification notice appears near the top of each upstream file with renamed local imports or with explicit stock modules replacing the Mathlib umbrella. The exact upstream license is included, with Git blob 261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64. No separate NOTICE file was present at this pin. No source was installed, vendored onto the project branch, or published to a remote in preparing this checkpoint.

The exact recursive import graph, original source Git blobs, Mathlib pin, and same Lean v4.35.0 are in UPSTREAM-SOURCE-PIN.json. The two selected imported targets, Dictionary and LemniscateIndep.Main, have a union closure of 16 modules and 3915 source lines, all externally depending only on Mathlib. The repository-wide StrongSix dependency and hundreds of Waldschmidt/transcendence modules are not needed here. This includes 12 files for the Dictionary alone; the four additional lemniscatic normalization files close the exact g₂=4, g₃=0 literal curve rather than assume a point-group change of variables, for which the pinned stock variable-change module provides coefficient/discriminant transformations but no evident affine Point AddEquiv. Cutting the three integral/real-normalization files would therefore introduce new analytic scaling/lattice reindexing and algebraic point-group work instead of using an already proved specialization. This note does not assert a smaller proof impossible.

Primary source: [Krisman, v4, §4.1 and §13](https://hexagonmath.org/2611.00170v4). The author's reported build/audit is not independently reproduced in this project. The source adapters here are new and currently uncompiled.

The r4 derivative also adds Lean module/public-visibility declarations to each
of the 16 vendored source files, with an additional explicit per-file notice.
The original upstream source headers and both prior import/notice derivations
are retained.  There are no edits to mathematical declaration statements, proof
bodies, namespaces, options, or imported module lists relative to r3.

Revision 5 adds a direct Mathlib import to SigmaQuasiPeriod only, with a new
per-file Apache change notice. It changes no mathematical source body.

Revision 6 adds one direct stock import apiece to Dictionary and RealLine,
with individual per-file Apache modification notices. No proof was edited.
