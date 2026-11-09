# Independent bounded review: actual local cohomology and Mayer–Vietoris

Reviewer: `/root/resume_relative_picard`. Producer: `/root/restore_differential_basis`.
Decision: **ACCEPTED within the seven-new-source scope below.**

I read all seven new Lean sources, the nine-point APPLICATION.json, the exact
consumed predecessor definitions and relevant pinned Mathlib source APIs. I
independently verified the source and evidence bindings with the adjacent
verify_bindings.py. I did not edit any producer source or contract, run a new
compiler replay, or reproduce the axiom audit. The fresh 30-source strict
replay and 321-declaration all-private recursive audit are producer evidence,
whose exact log, source, artifact and receipt hashes I checked.

1. The local generator is literally sheafification of the free-abelian
   representable used in Mathlib's cohomologyPresheafFunctor and H'. Its
   section equivalence uses evaluation at the original identity arrow.
   The naturality proof has the correct direction for coefficient maps.
2. The additive section equivalence uses the actual additive adjunction,
   not an arbitrary set bijection endowed with a new group structure.
   Ext degree zero and original restriction-section evaluation are matched.
3. Local affine H'1 vanishing takes an arbitrary actual Ext1 class, writes
   it as the connecting class for the original injective embedding and
   cokernel, and lifts its original section through the predecessor's
   arbitrary structure-sheaf-kernel theorem. The lifted Ext0 class kills
   the connecting class by exactness. The affine-open theorem includes
   empty opens; no affine Cech-to-derived theorem is assumed.
4. At the terminal open, the original free-abelian generator and original
   sheafified integer group both corepresent the same section functor.
   The resulting actual isomorphism has the correct inverse direction in
   Ext precomposition. Both inverse laws and additivity are proved. This
   matches Mathlib's original global H definition, not a renamed carrier.
5. The Mayer–Vietoris square is the actual intersection/U/V/top square in
   the full opens category. Its pullback and covering-sieve conditions are
   proved from the stated full union equality. Mathlib's short exact
   sequence of free sheaf generators is applicable to that square.
6. The boundary is the actual Mayer–Vietoris Ext connecting map followed
   by the proved terminal comparison. Surjectivity uses the original
   contravariant exact sequence and vanishing on both opens. The biproduct
   Ext comparison covers both factors; no summand or component is omitted.
7. AffineCoverHOnePresentation318 targets the original additive cohomology
   of the original structure sheaf and starts with original regular
   functions on the full overlap. It does not replace those functions by
   a proposed coordinate quotient or claim its kernel has been computed.
8. The contact consumer is exactly ContactGlobalSmooth318.Model units.
   I checked the actual finite and infinity chart embeddings, the affine
   infinity-open identification, original model integrality, and the
   full-cover theorem. The target is definitionally the same SourceHOne
   used by all five original quotient pullbacks.
9. The claimed boundary is appropriately bounded: a surjective additive
   map from actual overlap functions to actual H1. Explicit restriction-
   difference kernel, a quotient presentation, dimension five, fivefold
   spanning, rational linearity, Picard tangent comparison, Serre duality,
   Jacobians and isogenies are not accepted by this review.

Only the seven listed new modules receive new independent acceptance.
The 23 byte-identical predecessors are verified inputs, not newly authored
or newly independently accepted here. All 428 required baseline source
hashes match the original pinned commit manifest and current source bytes.
The receipt binds 150 producer artifact hashes and 44 producer evidence
files. All original sources, contracts and receipts remain unchanged.
