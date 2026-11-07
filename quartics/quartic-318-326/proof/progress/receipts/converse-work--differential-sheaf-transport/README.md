# Genuine affine differential sheaf transport

This packet supplies actual Mathlib Scheme.Modules morphisms and isomorphisms, not a parallel structure of local coefficients.

* PushforwardGlobalSections318 identifies actual affine pushforward global sections with the actual restricted-scalar module, through Mathlib's pushforward/sheaf natural isomorphism. No global-section compatibility premise is supplied.
* CanonicalDifferentialSheafMap318 uses the genuine tilde/global-section adjunction to construct the actual universal-differential sheaf morphism from Ω(S/R)-tilde to the actual pushforward of Ω(T/R)-tilde. Its exact global normalization and action on every universal differential are proved, as is uniqueness under that normalization. For an actual open immersion the genuine restriction/pushforward adjunction supplies the corresponding restriction morphism.
* TildePullback318 derives a genuine natural tilde pullback isomorphism with tilde of scalar extension. The derivation uses the actual module and sheaf adjunctions and their natural right-adjoint identification, then uniqueness of left adjoints. Its exact adjunction-unit normalization is proved. The actual open-immersion restriction version follows through Mathlib's restriction/pullback isomorphism. No assumed affine base-change sheaf isomorphism is used.
* ScalarExtensionTensor318 explicitly reconciles the categorical restricted-scalar instance with the already fixed algebra structure. This gives a T-linear tensor equivalence, then actual formally étale Kähler base change. Its pure-tensor formula is proved.
* EtaleDifferentialSheaf318 composes these actual isomorphisms into genuine differential-sheaf pullback/restriction isomorphisms. The principal-localization specialization derives both étaleness and the open-immersion condition from the genuine localization.

## Exact boundary

The canonical restriction morphism with proved global differential normalization and the constructed restriction isomorphism are both genuine objects. Their literal equality as sheaf morphisms has not yet been separately proved in this packet; the exact adjunction normalization and tensor formulas are available for that next comparison. Do not silently use that missing identification when combining the previously checked coordinate-form overlap equalities with these isomorphisms.

Actual specialization to every Weierstrass overlap, coherence on triple overlaps, and global relative differential/Hodge sheaf construction remain separate. The source elliptic-family relative Ω is not identified with the compact modular/PEL base canonical line. No arithmetic/analytic or model comparison is asserted.

## Replay

Run `bash verify.sh`. All five source modules are strictly rebuilt with debug.skipKernelTC=false, and all modules including generated/private declarations are explicitly imported for the recursive standard-axiom audit. No repository or Git edits are made.
