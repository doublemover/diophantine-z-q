# Attributed interior Riemann mapping port

Initial isolated5-source port of the complete interior Riemann mapping proof from official mathlib PR33505, head d43061d911b1aeae0788591da437a3b115098962, for pinned mathlib56a005855ea17e0b0958f73ec801ae140b0a1679. Upstream Apache2 license and Yury Kudryashov authorship are retained. This is an UNVERIFIED PORT, not a claim that an open PR or its changed APIs are kernel accepted.

Endpoint Complex.exists_bijOn_unitBall_map_eq_zero318: for an open simply-connected proper subsetU ofC and a pointx0 inU, constructs f:C→C differentiable onU, bijective fromU onto the open unit ball, with f(x0)=0. No boundary map, boundary extension, compact Riemann-surface classification, holomorphic sphere, genus, algebraization or original PEL model is supplied as a premise or inferred.

The proof chain is explicit: unit-disc Mobius shifts; compact zero-factorization and argument principle; Hurwitz preservation of nonvanishing/injectivity under locallyuniform convergence; actual log/root lifts; injective disk embedding and strict derivative improvement when not onto; local equicontinuity and Arzela-Ascoli compactness; extremal derivative produces surjectivity. The inherited proof bodies are retained under documented helper renames and module split, ready for distinct source review and focused hosted-only elaboration.

Dependencies:12of13 original imports exist at the exactpin. The missing UnitDisc.Shift is the195-line upstream source here, not a guessed API. The PR's one-line CompactOpen import visibility adjustment is unrelated to this isolated proof and is not applied. All upstream source bytes, helper renames, source hashes and license are bound. Existing project proofs and library files remain untouched.

## First hosted compatibility repair
Hosted Lean reached the unit-disc shift inverse and exposed a simplification mismatch between a pointwise forall and RightInverse. The right inverse now explicitly introduces its point and simplifies only double negation. The other four source files and all upstream bytes/license are unchanged. No local Lean run.
