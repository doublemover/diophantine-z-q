# Actual local triviality of the differential-orbit bundle

Strict-kernel PASS: 50 declarations in 5 modules, including 23 public theorems. Fresh replay uses `debug.skipKernelTC=false`, followed by an exhaustive recursive audit allowing only propext, Classical.choice and Quot.sound.

## Actual total space and local triviality

The total space is the existing genuine orbit quotient of pairs (z,q), with z in the upper half-plane and q complex, under the actual Gamma1(N) image acting by

    (z,q) -> (g*z, q/(g'(z))^2).

N>=5 is retained throughout the fine-level conclusions. The projection and norm are the previously constructed actual quotient projection and descended Petersson norm, not newly assumed structures.

`FiberQuotientCovering318` proves continuity of the actual action, proper discontinuity by projection of compact sets to the base, and freeness from the proved base freeness. Thus the total orbit quotient is itself a genuine quotient covering and local homeomorphism. The actual pair space is homeomorphic to the usual product, supplying the Hausdorff and locally compact structures.

`LocalFrameEmbedding318` uses each actual inverse sheet of the base covering to construct the coefficient map from that sheet times the complex numbers into the actual total quotient. It is injective by freeness, an open embedding by the actual total-space covering, and its image is exactly the total space over that base sheet. No continuity of a noncanonical coefficient-selection function is assumed.

`LocalTrivialization318.trivialization` combines these two actual open embeddings into a genuine Mathlib `Bundle.Trivialization complex projection`. `locally_trivial` proves that every actual base point is contained in one of these genuine local trivializations.

## Analytic transition and cotangent-square binding

`FrameTransition318` proves the actual local coordinate transformation, and identifies the descended Petersson norm in these actual trivialization coordinates. The coefficient changes by inverse derivative squared.

`CotangentTransition318.inverse_derivative_deck` proves that the derivative of an actual base chart transition is the derivative of its actual locally constant deck transformation. `cotangent_square_transition` consequently identifies the actual local trivialization cocycle with division by the square of the derivative of the actual analytic chart transition. That derivative is proved nonzero at every point of the transition source, and `analytic_cotangent_factor` proves analyticity of its inverse square. Thus the ordinary analytic line transition data, its exact cotangent-square coordinate rule, and its Petersson norm are proved for the actual quotient.

## Explicit remaining API/geometric boundary

The packet constructs actual local trivializations of the actual projection and proves their analytic complex-linear scalar cocycle. It does not yet register Mathlib's dependent `FiberBundle`/`VectorBundle` classes for the family of projection fibers, or identify the result with a separately constructed global cotangent tensor-square functor/sheaf. These are further packaging/identification steps, not assumptions used in the present proofs.

Compactification at cusps, extension of the line and metric there, the specified PEL/modular-family comparison, and arithmetic/algebraic global model identification remain separate. No claim about freeness or a line bundle on an arbitrary intermediate/diamond quotient is made.

## Replay

Run `bash analytic-differential-bundle/build-all.sh` from the parent directory. Accepted source hashes, dependency receipts and logs are in `receipt.json` and `SHA256SUMS`. Lean 4.35.0 and the pinned Mathlib revision are unchanged. No repository/Git files were edited.
