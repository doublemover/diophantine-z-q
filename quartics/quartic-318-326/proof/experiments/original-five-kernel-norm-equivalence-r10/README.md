# original-five-kernel-norm-equivalence-r10

DRAFT SOURCE REPAIR; HOSTED LEAN PENDING. No independent application acceptance or full theorem claim.

Revision of `original-five-kernel-norm-equivalence-r9` at `a2d615a4183174328321ea21d60879add229de3a`.

Make the unchanged dependent-open frame transport helper public and exposed so the original exposed frames definition can reference it across the module visibility boundary.

## Objects

The same R, arbitrary scheme X, structure p, full affine opens U,V, pointed deformation L and all Bool cover indices remain. frameAlongOpenEq retains exactly its arbitrary scheme/module/open equality inputs and output frame type.

## Coefficients

No ring, structure sheaf, scalar action, section module or unit coefficient changes. The helper still transports the entire unit-to-restriction isomorphism along equality of the original full opens.

## Exact maps

The helper body remains subst Z followed by exact e. frames still applies it to the original fullOpen_eq and OriginalThickenedFrameCocycle318.frames. stable and reconstruction retain the exact inner reduction-preimage and complete native preimage-cover proofs from r9.

## Diagnosis and proof route

The exact r9 hosted error is only unknown identifier frameAlongOpenEq inside exposed frames, with a diagnostic explicitly saying the private declaration exists but must be public to access here. In the existing public section, replacing private def by @[expose] def changes only the name/body visibility. It neither supplies a new geometric fact nor alters the dependent equality transport. The private helper was not permitted inside the exposed data definition; making its existing data construction public addresses that exact boundary.

## Full coverage

Every original full-open frame, both Bool cover indices and all sections remain quantified. No smaller cover, generic point, selected unit class or additional geometric restriction is introduced.

## Local hypotheses

The exposed helper has the identical type and body, with no new assumptions. Original affine/full-cover requirements, arbitrary-scheme scope, resource limits and trust settings are unchanged. The new public helper is included in fresh hosted declaration and recursive axiom auditing.

## Downstream

OriginalHOnePointedSurjection318 receives the identical original cocycle, overlap unit and reconstruction. Later representative_class unused-integrality scope risk remains unmodified and unverified; no downstream success is inferred from this visibility correction.

## Evidence and limits

Exact hosted failure, result, before source and bounded patch are retained. Every other root Lean file is byte-identical to its published predecessor. No imports/order, resource limits, admitted axioms, baseline or cache policy changes. Source review and structural checks are not Lean passes. Hosted strict compilation, recursive axiom audit and later-module checks remain pending.
