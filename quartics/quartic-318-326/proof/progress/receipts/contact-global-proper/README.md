# Construct the actual proper regular contact model

All five modules pass clean kernel replay and recursive audit of all 85 declarations, using only propext, Classical.choice and Quot.sound.

- ContactReciprocalBase318 constructs an explicit isomorphism between the original punctured t-line and its reciprocal s=1/t presentation. Both localization maps, their inverses, and their coordinate identities are proved.
- ContactReciprocalCover318 transports the entire source cover through that exact base isomorphism. It proves finiteness and etaleness of the reciprocal source presentation and finite normal Noetherian integral-closure models for both literal coordinate maps.
- ContactGlobalProper318 discharges both actual affine section-ring interfaces of Mathlib's globally glued relative normalization. Its normalization map is finite over P1_Q and its structural morphism is proper over Q. The original contact cover is the actual open dense source in this model, as proved in the predecessor packet. The projective line reused from the library is the contact t-line, not a claim that t is modular j.
- ContactGlobalNormal318 proves that the actual two chart rings and every actual structure-sheaf stalk are normal and Noetherian, and that the model is a Noetherian scheme.
- ContactGlobalRegular318 proves regularity of every actual stalk, with no height-one premise. Integrality over Q[t] gives dimension at most one, so the actual normal Noetherian chart closures are Dedekind and regular. The conclusion includes the generic point.

No finite/proper/normal/regular-model premise is supplied. The four rational twists remain arbitrary units. This packet does not formalize global smoothness over Q, a PEL source object or its comparison map, an integral model over a controlled ring of integers, good-reduction support, or the final Diophantine endpoint. Regularity over Q is not asserted to settle the integral arithmetic model.

Under the exclusive workspace compile lock, first build the two missing official pinned Mathlib dependency modules with build-regular-dependencies.sh, then replay run.sh. The dependency source and proof-object hashes are recorded in receipt.json. No dependency source was changed. Both dependency compilation and all packet checks use debug.skipKernelTC=false.

See receipt.json and SHA256SUMS. Independent review is pending. No shared branch, manuscript, or PR was changed.
