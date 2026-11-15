# Actual residue inertia explicit-kernel rewrite review

Source/current-application PASS for future hosted checking, not Lean acceptance. No local Lean/Lake.

After source713f004cc1b7db66242a9a6a70b4aa3e35c1e6dc3b1564e04ae08f6fa5833f38; application96f9bcb803ed92e046381fcf296c97b7c563845afe409011ede36f3117d35b06; manifestd76416eb20f0d1abb28abd84f31db187c8cae1457b0f01fcfc0dda62137fa038. All13 binding references verified. Full before/after source, current nine obligations, actual zero49 log/RESULT/intake and four native project snapshots read.

Exactly two rewrite sites change: finitePrime or infinityPrime is explicitly unfolded to its actual evaluation kernel, then kernel_inertia_iff is applied to that exact evaluation and original finite/infinity automorphism. The helper's required shape is literally e in inertia(ker p) iff p composed with e equals p, so exposing these aliases and providing p/e directly addresses the actual hidden rewrite-pattern failure. No ideal, evaluation, action, carrier, point or geometric conclusion is replaced.

The whole finite identity still retains every root and its nonzero condition; the actual finite branch theorem still uses original branch injectivity. The infinity theorem retains p.coordinate=0 and all eight normalized infinity centers, with the simultaneous-sign condition unchanged. No cancellation, chosen factor, finite sample, additional hypothesis or telescope change appears. Imports, resource options and proof bodies downstream of the two rewrite lists are unchanged.

Own zero49 intake74e1576ca2277ef5aeae35d4ab08a806321c778afa8513e0138ab57f4c500ed4 matches RESULT81844146122c6e777cb7fb72b6cd44f6a0c5b65b8e73612f90a9a286dbd82ef0 from run43661685475. CharacterFields3.023s and FractionField3.474s are full-module passes; ResidueInertia1.769s fails at precisely these two rewrites after41 successful commands. The unchanged helper has no earlier reported error within that failed module, but this is NOT a separately completed full-module/kernel acceptance for the helper. Later OrderAutomorphisms remains unreached.

Native type inference and all subsequent proofs still require hosted verification. Exact all-copy/current-packet propagation is separate. No full lane, PEL endpoint or arithmetic closure follows from this source review.
