# Actual overlap diagrams and rigidified transitions

This draft advances beyond a family of isomorphisms on a single unnamed test:

- `ActualOverlapDiagram318` constructs the actual double fiber product of
  `f : U → T`, the triple fiber product of adjacent pairs, all three edge
  maps and the diagonal. It proves every endpoint and structural-base identity.
- `ContactRigidifiedPathComparison318` compares iterated and direct original
  rigidified pullback along named equal test paths. The relative-class equality
  supplies a unique actual compatible path isomorphism.
- `ContactOverlapTransitions318` uses the exact overlap diagram over the
  original contact field base. Matching original relative classes on the
  double overlap supply an actual compatible overlap isomorphism. Its three
  pulled-back edges, after the explicit path comparisons, satisfy a cocycle
  equality of actual module-sheaf morphisms on the full triple overlap.

The index coverage is no longer merely an arbitrary collection of lines on a
single scheme: double and triple overlaps and all their maps are explicit.
The generic diagram needs no cover hypothesis, so it also applies to an fppf
cover. The contact specialization uses all-scheme-test rigidity over the exact
field base, not an unsupported arbitrary-nonfield-base generalization.

## Precise remaining boundary

The path comparison is selected from proved original relative-class equality
and rigidity. This packet does **not** identify its underlying isomorphism
with the canonical unrigidified module-pullback composition comparison.
Consequently the cocycle is explicitly normalized by those selected path
comparisons; it is not silently declared to be a standard `Scheme.Modules`
descent datum. That canonical comparison is the next obligation. The existing
`PullbackPathComposition318.assoc` theorem is a potential source for it, not
a theorem applied by this packet.

No object is glued here. Effective descent of original locally free rank-one
module sheaves, rigidification gluing, identification with associated-fppf
sheaf values, degree zero and representability remain further work. No
unconditional arithmetic result is claimed.

## Validation

Three new modules use 34 byte-identical producer copies and one repaired
producer. Five producer modules originate as drafts from `rigidified-transition-coherence`.
The first hosted check of that predecessor packet failed in
`RigidifiedIsoCoherence318.compose` before later modules could compile. This
superset repairs the implicit-transparency mismatch using explicit typed
`mapIso` terms and explicit projection reductions, without changing statements
or underlying maps. The failed original bytes remain preserved; see
`SOURCE_REPAIRS.json`. Source/hash/import/placeholder validation passes. Local Lean compilation was
not run, as instructed. Hosted strict compilation, recursive axiom audit and
independent acceptance are pending. The audit file is input, not a receipt;
old receipts are not reused as evidence for the new modules.
