# Current observed Hausdorff and coercivity source contracts

Run43592150561 at75be14ed25ed39f46289f1c69914810afd46068c. The exact candidate hashes and all three own artifact ZIP/RESULT/log/intake digests are in FIRST-TWO-MANIFEST.json. These are isolated source candidates, not accepted Lean modules or successor packets. No local Lean/Lake was run. Earlier SphereAffineNormalization and SiegelNormalization full-module passes are distinct observations; neither proves these new modules.

## 1. Required source input

Hausdorff: the private separation helper requires an actual open embedding f:X→Y from a Hausdorff space. The native declaration is Topology.IsOpenEmbedding, not an implicitly introduced unknown global identifier. Mathlib_Topology_Defs_Induced.lean defines it inside namespace Topology; Mathlib_Topology_Maps_Basic.lean supplies isEmbedding/isOpenMap. Only that fully qualified name is substituted in the existing helper input.

Coercivity: Complex.normSq_pos.mpr needs τ≠0, supplied by the unchanged PELOriginalSiegelNormalization.parameter_ne τ hτ. Positivity and the lower bound need the intended upper-half-plane hypothesis hτ:0<τ.im. Exactly normSq_positive, coercive_positive and energy_lower acquire explicit hτ binders, in the order already used by their consumers. Literal public telescopes change. These previously failing declarations are not accepted unconditional positivity claims; the candidate restores the section's intended premise rather than claiming an unrestricted result or hiding an added assumption. coercive and sum_squares_identity remain hτ-free.

## 2. Actual constructed objects

Hausdorff retains Completed b, the original FourRootGluedTopology.topology b defined by the coinduced two-chart map, the exact finiteChart and infinityChart and the continuous projection into OnePoint ℂ. It does not substitute the disjoint-sum topology or transport a topology from the PEL curve.

Coercivity retains the actual Siegel energy τ x and coercive τ = alpha*τ.im/5*min 1 (1/Complex.normSq τ). The same beta/alpha constants, complex parameter, real Fin2 vector and original period normalization remain. The new proof does not choose a different norm, weaker energy or surrogate matrix.

## 3. Domain and index coverage

Hausdorff keeps every b:Fin4→ℂ and all finite/infinity cases, including all eight normalized InfinitySigns. No injectivity/distinctness assumption on b is added. All four case branches and exact infinity centers remain byte-identical.

Coercivity covers every τ with positive imaginary part and every x:Fin2→ℝ, including zero vectors. Both coordinate positions and the full real domain remain. No rational approximation, bounded vector test or finite sampling replaces the universal inequality.

## 4. Maps, directions and compatibility

The Hausdorff helper still separates by images of disjoint open subsets under the same native f. Its injectivity/disjointness proof, finite/infinity open embeddings and mixed-pair projection pullbacks are unchanged. Qualification resolves the intended namespace without introducing a new map or hypothesis type.

For coercivity, set m=min 1 (1/n), n=Complex.normSq τ, U=((beta+1)*x0−2*x1)^2 and V=((beta−1)*x0+2*x1)^2 as before. The existing h1:m*U≤1*U and h2:m*V≤(1/n)*V are added directly. mul_add rewrites m*(U+V), add_le_add preserves inequality direction, and ring identifies 1*U+(1/n)*V with U+V/n. This addresses the observed residual without asking nlinarith to normalize the inverse expression. It requires no new denominator assumption and preserves the same hsum/hall route.

## 5. Scalars, signs and local conditions

All Hausdorff chart/projection formulas, square powers, normalized infinity signs and branch parameters are unchanged. No chart or boundary is collapsed.

All coercivity constants5/20, factor4 in hsum, beta±1, factors2 and squared terms are unchanged. The original positive τ premise supplies nonnegativity for alpha*τ.im/20; beta_sq and sum_squares_identity proofs are unchanged. No Euler/scalar factor is omitted. Only the three explicit positivity binders and the hsmall proof presentation change.

## 6. Exact downstream object identity

PELOriginalCompletedContactBiholomorph318 installs FourRootCompletedHausdorff318.hausdorff branches as T2Space on the exact Completed branches carrier. Its comparison is the original completedMap promoted through DenseTargetOpenComparison.homeomorph, not a cardinality bijection, and includes all ramified fibers and eight infinity points. The local T2 instance, comparison and infinityEquiv/infinity_card passages are preserved in primary evidence.

PELOriginalThetaConvergence318 consumes coercive_positive τ hτ in summability and energy_lower τ hτ on the complete integer-pair vector. ScaledThetaConvergence uses the same two statements with its existing positive scale. ThetaSecondBounds, ThetaHolomorphy and ScaledThetaHolomorphy consume the same positive constant. Those exact source files are retained. The explicit hτ telescope is the application order those consumers already require.

## 7. Exceptional cases

Hausdorff retains finite/finite, finite/infinity, infinity/finite and infinity/infinity separation, without a generic-locus restriction. The continuous projection formula includes the zero infinity coordinate. Unknown-helper downstream holes in the log are observed, but their complete disappearance after qualification is a hypothesis until hosted replay.

Coercivity excludes only the already intended non-upper-half-plane inputs by making hτ explicit. Zero vector and all signed real coordinates remain. There is no extra premise asserting normSq positivity, hsmall or the final inequality; these are proved from the original data.

## 8. History and evidence

Both zero-r42 and cotangent-r48 own logs report the identical unknown IsOpenEmbedding frontier; their RESULT packet_sha256 values match exact published intakes. The torsion-r22 own log reports the omitted hτ errors, incorrect hτ application to normSq_positive, inverse-normal-form hsmall failure and positivity failure. All authentic artifact metadata, ZIP digests and logs are retained. This candidate does not claim earlier unrelated approvals cover it, or that absence of an error in a failing module means an independently passed theorem.

The initial primary guessed Maps/Defs path returned404 and the actual pinned tree identified Defs/Induced and Maps/Basic. The successful primary content bytes are Git-blob-verified against their API metadata at mathlib56a005855ea17e0b0958f73ec801ae140b0a1679. This provenance is retained without treating the failed lookup as API evidence.

## 9. Verification boundary

Imports, production resource/trust options, complete source domains and all unrelated proof bodies are unchanged. No sorry, axiom, placeholder proof or new runtime resource override is added. Fresh independent source/contract review is required, then exact-copy propagation with per-packet nine machine obligations and own evidence. Current candidates have not run under Lean, passed a kernel check, completed a recursive-axiom audit or established the whole arithmetic theorem. The hτ telescope correction is explicitly disclosed rather than called literal statement preservation.
