# Application contract: affine overlap equations produce a coalgebra

Draft only. Exact source and document bindings are in `APPLICATION.json`;
producer locations and hashes are in `DEPENDENCIES.json`. This does not change
accepted-baseline sources, manuscript passages or historical verdicts.

1. **Required inputs.** The retained `AffineOverlapCoaction318.homEquiv`
   takes an actual map between the first and second scalar extensions of an
   S-module N over the literal double tensor ring. The retained diagonal
   theorem needs the actual evaluation equation. Faithfully flat reconstruction
   needs an actual coalgebra of the original extension/restriction adjunction,
   with an actual identification of its object with the original line sections.
2. **Constructed objects.** The double and triple rings, three vertex maps
   and three pair maps are exactly `AffineCechRings318`. Each edge is inverse
   first scalar-composition comparison, literal scalar extension of the
   overlap morphism, then second scalar-composition comparison. This is not
   an arbitrary choice of equal-dimensional modules or morphisms.
3. **Coverage.** R and S are arbitrary commutative rings with the given
   R-algebra structure; no field, domain, reducedness, Noetherian or generic
   rank assumption is used in the conversion. Tensor induction covers every
   element, not just pure tensors or generic points. The reconstruction uses
   the retained all-prime rank-one descent and full principal-open cover.
4. **Transition directions.** The cocycle is edge12 followed by edge23 equals
   edge13. The third-vertex comparison sends the full tensor
   `(a tensor (b tensor c)) tensor n` to `a tensor (b tensor c*n)` in the
   twice-applied original comonad. Thus edge13 is original comultiplication;
   edge12-then-edge23 is the original comonad map of the candidate coaction.
   `restrictedComponent` explicitly reconciles the R action through the first
   S factor using the actual restriction-of-scalars composite identity.
5. **Hypothesis checks.** The tensor comparison and scalar-composition
   equalities use the exact original ring maps and their six endpoint
   identities. Both coalgebra axioms are derived from module overlap equations.
   Faithful flatness is required only by `AffineCocycleLine318`, where the
   existing `faithfullyFlat_algebraMap_iff` discharges the exact ring-map input.
6. **Consumer identity.** `coalgebra_object` is literally N and
   `coalgebra_coaction` is literally the already defined `homEquiv`. The
   final consumer specializes N to `OriginalLineAffineModel318.sections S L`
   and uses the identity isomorphism, not an unrelated module equivalence.
   The retained `AffineCoalgebraLine318.pullbackIso` supplies the actual
   original line-sheaf pullback comparison. Its coaction compatibility is
   exposed again with this exact original candidate coaction.
7. **Coefficients and exceptions.** The scalar actions are original
   `ModuleCat.extendScalars` and `restrictScalars` actions. Triple-coordinate
   comparisons are canonical composition and tensor-pushout comparisons.
   No scalar, norm, Euler factor, degree or polarization is discarded or
   inferred. Nonreduced rings and every actual prime remain in scope.
8. **Downstream boundary.** This closes a module-level cocycle-to-coalgebra
   conversion in source. It does not prove that the retained geometric
   sheaf-to-module overlap correspondence transports all geometric diagonal
   and triple identities to these exact module identities. That compatibility,
   arbitrary-scheme and rigidification gluing, associated-sheaf comparison,
   degree zero and representability remain further work. No final arithmetic
   premise or historical disposition is changed.
9. **Evidence and acceptance.** Five new sources and fourteen exact copies
   are source-bound. Eight copied scalar/basechange modules are retained
   drafts; partial historical markers are not claimed as successful checks.
   Source/hash/import/placeholder validation passes. No local Lean build ran;
   complete hosted strict replay, recursive audit and independent acceptance
   are pending. This application contract does not grant acceptance.

## Revision r2

This19-source revision retains18 source files byte-for-byte and changes only
ScalarExtensionComposition318 proof elaboration. Explicit tensor typing follows
map_smul, and the inverse calculation exposes both original hom applications
and uses the exact natural-isomorphism component cancellation lemma. The full
tensor formulas, actual maps and every theorem statement remain unchanged.
Hosted run42575074470 at f58c577 compiled the first12 modules, then failed at
these two proof steps; its exact RESULT and log are retained. The original
packet is unchanged. No local Lean ran; full hosted checking, recursive audit
and independent acceptance of this revision remain pending.
