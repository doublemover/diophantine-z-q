# Canonical actual differential restriction comparison

This packet closes the explicitly retained map/isomorphism identification from differential-sheaf-transport.

`CanonicalRestrictionComparison318.restrictionIso_hom_eq` is literal equality of genuine Scheme.Modules morphisms. It proves that the constructed formally étale differential restriction isomorphism is exactly the canonical universal-derivative restriction morphism whose action on actual global differentials was proved upstream. Consequently `canonical_restriction_isIso` derives that the actual canonical restriction morphism is an isomorphism; no compatibility or isomorphism premise is supplied.

The proof chain is explicit:
1. TildeComparison318 binds the natural tilde pullback/scalar-extension comparison to every actual module map through the two genuine composite adjunctions. Its global formula retains the actual pushforward/global-section isomorphism and scalar restriction.
2. CanonicalEtaleComparison318 proves that the actual étale tensor isomorphism has the actual universal Kähler map as its module-adjoint, by the exact 1-tensor formula. It then identifies the actual sheaf pullback isomorphism's adjoint with the canonically normalized universal-derivative sheaf map. This also proves the canonical pullback morphism is an isomorphism.
3. CanonicalRestrictionComparison318 uses the actual open-immersion restriction/pullback comparison and its adjunction-unit normalization. This gives exact equality of restriction morphisms, not merely abstract existence of some sheaf isomorphism.

The theorems are generic for actual commutative algebra towers, formally étale maps, and actual open immersions. Genuine principal localizations satisfy the latter conditions by the preceding packet. No coordinate algebra, derivative, sheaf, or categorical adjunction is replaced by a parallel structure.

Remaining work: bind these canonical restrictions to every actual Weierstrass overlap map, prove concrete overlap coherence, and assemble the global relative-family differential/Hodge interpretation. This does not identify elliptic-family relative Ω with the compact modular/PEL base canonical line, and it does not establish the remaining global source realization or unconditional soundness.

Run `bash verify.sh`. All three modules are strictly rebuilt, and every module including generated/private declarations is explicitly imported into the recursive standard-axiom audit. Frozen upstream sources are unchanged. No repository or Git edits are made.
