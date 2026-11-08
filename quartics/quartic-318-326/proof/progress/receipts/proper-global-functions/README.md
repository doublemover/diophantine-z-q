# Actual structure-sheaf pushforward over domain bases

This packet proves the canonical O→π_*O morphism is an isomorphism for the actual completed short-Weierstrass family over every domain coefficient ring. It does not assume a global-functions identity.

IntegralRetraction318 proves that an integral ring extension into a domain with a ring retraction is bijective: the retraction kernel contracts to zero and is therefore zero. ProperGlobalSections318 applies Mathlib's universally-closed global-section integrality theorem and the actual infinity section. ProperAffineSections318 proves integrality and an actual ring retraction on every affine base open, handles empty opens explicitly, and detects the genuine sheaf-map isomorphism on the affine basis. Its general unitMap_isIso theorem requires an integral source, a universally closed morphism, and an actual section. family_unitMap_isIso specializes to the constructed Weierstrass scheme with its already checked properness and integrality.

Strict sequential replay and exhaustive recursive axiom audit pass: 11 declarations in three modules; only propext, Classical.choice and Quot.sound. Run run.sh while holding compile-coordination/heavy.lock. Predecessor artifacts are used, not freshly rebuilt in this producer replay.

The family theorem requires IsDomain R. No assertion over arbitrary nilpotent coefficient bases is made. Identifying the intrinsic relative differential sheaf with the global invariant line, the canonical Hodge isomorphism, and the particular compact modular/PEL source remain separate.
