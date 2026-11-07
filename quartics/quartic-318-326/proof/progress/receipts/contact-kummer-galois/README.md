# Actual four-contact Galois group

This packet constructs the sixteen actual root-sign automorphisms of the twisted four-contact field and of its original four-polynomial tensor algebra. It proves their distinctness, exhaustiveness, Galoisness, automorphism cardinal16 and exponent2. The source specialization keeps arbitrary nonzero rational twists of t, t-32, t-76832 and t+343.

## Exact proofs

- `FourRootAutomorphisms318` constructs the actual quotient-ring root-negation equivalences and their tensor products. It proves their action on all four generators, generator squares/nonvanishing, distinctness of all sixteen sign choices and that each sign map squares to the identity.
- `FourRootGalois318` transports these maps through the genuine existing tensor/field equivalence. The actual automorphism count is bounded above by the actual field degree16 and below by the sixteen constructed maps. The standard finite-extension criterion then proves Galoisness. Equal finite cardinality proves that the sign maps exhaust the automorphisms.
- `ActualKummerGalois318` transfers Galoisness back to the actual original tensor algebra and proves every automorphism squares to the identity. Its source-specialized results have no supplied Galois, degree, normality, automorphism-count or involution premise.

## Remaining boundary

This is the actual twisted contact t-cover algebra, not an identification with the PEL/Shimura source curve and not the modular j-cover. The actual source twists, source curve/function-field comparison, integral geometric realization and unconditional Diophantine theorem remain open. No separate classification theorem identifying an abstract group with a preselected F2-vector space is assumed or claimed; the sixteen explicit sign choices, cardinality and exponent2 are proved directly.

## Replay

Run `bash run.sh > verification.log 2>&1`. All three modules are freshly checked with `debug.skipKernelTC=false`, followed by an exhaustive recursive axiom audit. Only propext, Classical.choice and Quot.sound are allowed. The frozen `contact-kummer-field` and exact polynomial/base-change packets provide the actual preceding field construction.
