# Actual intrinsic tensor normalization

This packet continues the genuine cotangent tensor-square construction on the
complete contact normalization for arbitrary nonzero rational twists c_i.
It uses the actual five affine chart embeddings and the actual universal
relative differential sheaf over Q.

## Checked content

- Sheafification, tensor congruence and open restriction preserve pure tensors
  with the exact multiplication normalization. No unspecified nonzero scalar
  occurs in the tensor frame.
- On each entire finite branch chart, t-a_i=c_i^(-1) z_i^2 and
  Dt=(2 z_i/c_i) Dz_i. These are whole-ring and universal differential
  identities, including the branch point.
- The inverse local cotangent frame at scalar one is exactly the universal
  coordinate differential: Dz_i on branch i and Du at infinity, with
  u=c_0/y_0. The generic proof is applied to the actual chosen frame, and
  `branchFrame_eq` / `infinityFrame_eq` check that comparison exactly.
- `localSquare` is the genuine tensor square of that generator.
  `q0_normalized` and `q1_normalized` identify the previously constructed local
  bicanonical sections with their displayed regular coefficients times this
  square. The coefficient definitions are unchanged from tensor-foundation.
- The generic `finite_cleared` ring lemma supplies the algebraic identity used
  next to compare the local q0 with Dt tensor Dt after multiplying by the
  contact quartic. Its actual-chart specialization is separate continuation.

The two concrete coordinate comparison proofs use inferred proposition-valued
`def` aliases to preserve exact categorical instances and keep kernel checking
bounded. They are proof terms checked by the kernel, not axioms or hypotheses.
The recursive axiom audit includes these aliases and all generated declarations.

## Boundaries

This packet does not yet prove equality on full chart intersections or glue
q0/q1 to global sections. It makes no global triviality, genus, canonical-degree,
PEL identification or Kodaira-Spencer comparison claim. Source/infinity
intersection maps are being provided in a separate packet; none is assumed here.

## Validation

`MODULE_ORDER.txt` gives the strict compilation order. All sources use the
canonical pinned Mathlib modules. `JoinedAudit.lean` checks every declaration
(including private/generated declarations) in these ten modules and the thirteen
contact/tensor predecessor modules against only propext, Classical.choice and
Quot.sound. Exact results and source bindings are in receipt.json.
