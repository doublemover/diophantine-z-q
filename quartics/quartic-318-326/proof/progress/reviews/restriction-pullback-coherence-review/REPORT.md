# Bounded restriction/pullback coherence review

Accepted the exact frozen RestrictionPullbackCoherence318 source at receipt93ae99555d33acb756a3431660adc288e6bd3358a12808895a18b11f18931a0d. All six public proof bodies, the application and retained strict/audit evidence were read. No compiler replay or shared source edits were performed.

1. The actual morphisms f and g are scheme open immersions; M and q are original arbitrary module-sheaf objects/maps. The open-immersion hypotheses are present where needed, with no unstated flatness, reducedness or line-frame premise.
2. The restriction/pullback comparison is the original Mathlib leftAdjointUniq construction. The first and component transpose identities use its defining hom-equivalence identity, not uniqueness of arbitrary isomorphisms.
3. The unit comparison is the original pullbackObjUnitToUnit isomorphism; its adjoint is the literal structure-sheaf unitMap. The actual restrictUnitIso is the original open-immersion appIso, including inverse scalar normalization.
4. restrict_unit checks that exact normalization by original adjunction injectivity and every-open app/appIso cancellation. It is not only an equality of line classes or a claim that the two unit objects happen to be isomorphic.
5. restriction_composition_unit uses actual restriction units, original pushforwardComp and original restrictFunctorComp. The every-open proof reduces to the same original presheaf restriction composition, retaining equality transports.
6. adjoint_restrict_composition is naturality of that exact pushforward comparison precomposed by the original composite unit. Arbitrary q is retained.
7. composition has exactly r_(f≫g) followed by pullbackComp.inv on one side and restrictComp.hom, restrict(f).map(r_g), then r_f on pullback(g)M on the other. The official conjugateEquiv_pullbackComp_inv is used in the correct contravariant order. No unproved associator or freely chosen normalization is substituted.
8. Final check3 and private-inclusive7/1 audit pass; the earlier rewrite/functor-alias failures remain transparently retained and are not counted as successful checks. Exact source and dependency pins, final frozen/working source bytes and standard-axiom audit evidence were verified. The reviewer offered typed-rewrite and explicit functor-alias suggestions during debugging, but did not author or edit these proofs. Adjacent original line-frame/scalar work belongs to the reviewer and is excluded from self-approval. The canonical unit-composition predecessor has its own separate group-worker acceptance.
9. This acceptance is only for these exact normalization maps and their intended application to actual frame restriction. It is not acceptance of the still-separate full frame-coherence theorem, unconditional extracted transitions or norm8, pullback tensor coherence, represented Picard/Jacobian, or final318/326 closure.

No discrepancy or required correction found at this bounded scope.
