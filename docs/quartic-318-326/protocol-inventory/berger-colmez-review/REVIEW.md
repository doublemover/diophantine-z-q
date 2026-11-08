# Independent review of the V13 local monodromy application

Decision: accepted within the packet's bounded mathematical and source-adoption scope. Reviewer: model worker /root/restart_contact_field, not an author of this application or the cited manuscript argument; model identifier is not exposed in this runtime. Reviewed on2026-11-08. This is an independent statement/definition/application review, not a new proof of the published monodromy theorem, a Lean replay, or approval of an unprovided manuscript edit.

The target is recovery-hodge-0358/berger-v13-review, receipt SHA256 fc6dbc84e96744a9c702bd0854d039d69397dc4cb5abf2132d33823aa489c616. The exact four public artifact hashes, all seven actual V13 excerpt hashes, three primary PDF hashes/byte counts, and four neighboring source/decision bindings match. The active V13 whole-file hash is9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd.

## Primary reading and independent inference

Before reading the packet's verdict, I read the actual V13 representation constructions, both monodromy sentences and Pan consumers, the de Rham lemma, Berger's author Theorem0.7 and surrounding definitions, his complete relevant errata section, and Colmez's published local setup/§0.2/Theorem0.1. I visually inspected printed Colmez page118, not just its faulty OCR. I then read all nine obligations and the complete frozen record. I also read the published Calegari pages611–612 and624 for the precise downstream local condition. Tools were read-only cloud shell/Python/PyMuPDF, direct source text, and image viewing; only this separate review folder was written.

Colmez, Espaces vectoriels de dimension finie et représentations de de Rham, Astérisque319(2008),117–186, Theorem0.1, is an actual published proof of the required implication. The source defines a continuous finite-dimensional Q_p representation of G_K, K finite over the Witt fraction field of a perfect residue field; de Rham means full B_dR period dimension, and potential semistability means semistability after some finite local extension. For the actual Q_5 base all these field hypotheses hold. There is no negative-weight, residual-image, ordinary, or crystalline restriction on Theorem0.1.

Let E be the fixed finite coefficient field and W the underlying Q_ell representation of r_ell. Its dimension is2[E:Q_ell], and the already stated de Rham lemma supplies full de Rham admissibility for this W, not just a list of Hodge–Tate weights. Colmez supplies one finite local extension L/Q_ell over which W is semistable. The natural comparison map is functorial for all Galois-equivariant Q_ell endomorphisms, so E acts on its period module and the comparison commutes with that same E-action. Thus it is the original r_ell which is potentially semistable.

For explicit coefficient-embedding coverage, extend coefficients to one finite normal field containing every embedding of E. The separable coefficient algebra then splits into idempotent factors. Applying those idempotents to the E-linear comparison recovers each original rank-two coefficient conjugate, all over the same L. This only makes explicit the packet's scalar-splitting sentence; it does not require separately chosen local extensions or replace r by its determinant/double/trace. Forgetting E-linearity and restoring its commutant are the comparison maps actually needed.

The finite local L is not the bounded global splitting field L′ used earlier in the height argument. No extension-degree bound or contribution to the global isogeny budget is claimed. Nor is semistability descended to Q_ell: de Rhamness was descended first, then monodromy supplies a possibly different finite local extension. No integral lattice equality, normalization of N, or period scalar is consumed. At ell=5 this supplies exactly the local geometric property needed by the published Pan formulation; oddness, irreducibility, finite ramification and weights remain separately supplied premises.

## Nine-obligation decision

1. Source hypotheses: accepted. Finite E gives a genuine finite-dimensional continuous Q_ell representation, and the predecessor supplies de Rhamness. The actual Q_5 residue field is perfect.
2. Constructed objects: accepted. The matrix-unit multiplicity representation r_ell and its constant E-action are preserved; no unrelated geometric representation is substituted.
3. Domain/index coverage: accepted. The argument is pointwise for every relevant ell and finite coefficient field, with one extension for all its embeddings. Actual downstream use is ell=5, and no uniform family bound is asserted.
4. Transition/comparison maps: accepted. Restriction of scalars, local restriction and the natural semistable comparison retain E by functoriality. De Rham descent and potential semistability are correctly distinguished.
5. Identity of consumed object: accepted. The actual r_5 is potentially semistable, not only its restriction to the earlier global field or a related summand.
6. Coefficients/normalizations: accepted. The argument is rational, Tate weights remain0,−1, and no integral comparison or explicit monodromy normalization is inferred.
7. Local conditions: accepted. Local existence is the right Pan premise; unramifiedness away from5 is a different argument. No good-reduction or ordinarity assumption is inserted.
8. Exceptional cases: accepted. Berger's intermediate negative-weight restriction is not a hypothesis of the final theorem. The p≥5 restriction belongs to Pan, and is satisfied at5; it is not imposed on monodromy itself.
9. Downstream consumption: accepted within the named boundary. Both V13 call sites consume only this local premise. This result alone gives no modularity, conductor bound, source/PEL identification, Arakelov estimate, or final318/326 witness.

## Version and integration limits

Berger's author-format article, Theorem0.7/Corollary5.22, and current errata are correctly distinguished from his final Inventiones typesetting. The errata address substantive internal details: Robba coefficient field, logarithm domain, transposition convention, density rather than equality, interval/ring conditions, and the scalar normalizing N. I found no withdrawal of the endpoint statement in the inspected list, but do not claim to have reproved all corrected arguments or completed author-to-final comparison. The published Colmez proof supplies a separate legitimate source; it is not evidence of byte identity for Berger.

The current V13 bibliography does not yet cite Colmez for these sentences. My acceptance covers the exact published-source application recorded in this packet, with **explicit source adoption still pending**. It does not mark that change incorporated or approve any future patch without its exact text/hash. Berger's final-typeset comparison remains an open documentation item if that specific source identity is desired. The actual geometric/de Rham producers and Pan's remaining source-version qualifications remain separate; this review does not erase them.

No issue requiring a mathematical repair was found in this bounded application. No shared source, receipt, or manuscript was edited.
