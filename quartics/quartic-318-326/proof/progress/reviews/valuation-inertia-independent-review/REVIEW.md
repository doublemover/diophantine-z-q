# Actual finite-contact valuation inertia: bounded independent read

## Decision and provenance

Accepted for the exact six-source valuation-inertia application and its separate one-source canonical-prime consumer. The reviewer read every new source body, both nine-obligation contracts, the named immediate predecessor maps, and the relevant pinned Mathlib definitions. No source was edited, no compiler was run, and no hosted audit is implied.

The author is restart_contact_field; the reviewer is restart_modular_curve. The reviewer previously accepted the order/residue-inertia and full-order-automorphism consumers and now reread their actual interfaces. This is a new read of the changed valuation route, not a second independent review of those predecessor results. The reviewer's unrelated finite-flat rank helper is not a dependency. No blanket acceptance of the entire earlier contact construction, Galois theory, final arithmetic proof or manuscript is claimed.

The exact targets are receipt94e102e9370324ca232cbaadbeac7e4a4c6e23bdd911bf96222c61099df90798 and receiptf448d1ac5389351955b22458c434abc4488892c574a1ac2fc966830a2c2d3129. Their APPLICATION hashes are2c7b60503fdc13becebddcb5440fa006eeb54aea86f4e8ea64c102930cb54b77 and099480084bd6277c77622d19779cf291031b9662330095e6a17a299bcf18751f. SOURCE-BINDINGS.json pins the complete inspected target/evidence/dependency set.

## Actual object and hypothesis checks

SourceBranchValuation318:14–39 keeps arbitrary c : Fin4 → Q-units and the original SourceOrder c embedded in SourceFractionField318.L c by embedding c. Whole-source integral closure is consumed from SourceGlobalAffine318.source_integrallyClosed, not inferred from a punctured ring. Finite algebra over Q[t], domain and integral extension give Noetherianity and dimension at most one, establishing Dedekind for the whole order. SourceFractionField318.actual_fractionField uses the original generic-fiber equivalence; embedding_on_polynomial proves the compatibility used for polynomial injectivity.

At lines41–78 the kernel of an actual R-algebra point p is prime. The literal X−a_i lies in that kernel and is nonzero by the proved polynomial embedding, so it is a genuine HeightOneSpectrum point. The valuation ring is exactly HeightOneSpectrum.valuationSubringAtPrime inside the original Raw field. Pinned AdicValuation:475–514 defines this via the embedded localization subalgebra, provides its actual algebra/tower and IsLocalization instances, and equates it to the adic valuation subring. This is not a replacement DVR chosen by existence.

## Localization and full residue identity

PrimeLocalizationInertia318:16–38 proves both inclusions of the prime-complement image under e from P=P.comap e, then uses ringEquivOfRingEquiv for the actual localization. The extension has the exact algebraMap formula. Lines43–64 prove both directions between triviality modulo P on every original order element and equality of the entire local residue map. The converse uses localization ringHom_ext, not a bare generator or quotient-image assertion. Lines67–81 then use actual residue surjectivity to identify the full induced residue-field automorphism.

The pinned AtPrime theorems identify units with the complement of P and the pullback of the maximal ideal with P. The pinned local residue mapEquiv uses an actual ring equivalence and its inverse; its residue action is mapAut composed with the ring action. All required local-ring and localization hypotheses occur in the constructed objects. No algebraic-closedness or rational residue point is assumed.

SourceValuationInertia318:40–56 proves the ambient square for every valuation-ring element using localization extensionality and the original extend_embedding identity. Consequently the localized ring action is not an unrelated automorphism with the same abstract label. Lines61–74 identify full local residue identity with the previously proved actual Ideal.inertia condition.

## Exhaustive field automorphisms and actual decomposition group

SourceOrderFieldEquiv318:17–48 proves injectivity of the literal field extension by the injective order embedding, surjectivity by the exhaustive original four-root field signs transported through rawEquiv, and multiplicativity by fraction-ring extensionality. It therefore constructs a full MulEquiv of actual automorphism groups, not a cardinality-only argument. The reviewed predecessor extend is the concrete id_K tensor e conjugated by genericFiber; extend_sign is proved on the whole original field. FourRootGalois318.signAutomorphism_surjective has the actual Independent/characteristic-zero input supplied for the original parameters, not an unsupported arbitrary multiquadratic algebra claim.

SourceValuationDecomposition318:27–77 uses Mathlib's genuine decompositionSubgroup, namely the stabilizer of the embedded ValuationSubring under all K-algebra field automorphisms. orderAut is the inverse of the actual field MulEquiv. Its prime preservation is proved through units of the localization and both directions of the restricted ring automorphism. action_eq_local is equality on the entire valuation ring. The actual inertia definition in RamificationGroup.lean is the kernel of the action on the full residue field; mem_inertia_iff unfolds exactly that kernel and uses the established action equality. A custom subgroup has not been renamed as valuation inertia.

## Both directions and exact downstream conclusion

SourceValuationFullInertia318:27–35 shows order inertia preserves the exact prime. ofOrder:39–61 constructs a genuine valuation stabilizer from any prime-preserving order automorphism; forward preservation uses the ambient square, and reverse preservation explicitly uses the inverse local ring equivalence. The finite-contact inertiaEquiv:70–83 retains both inverse identities. This is an Equiv of the underlying inertia sets, sufficient for the stated cardinal theorem; no newly packaged multiplicative equivalence is claimed there. inertia_card follows from the original full-order inertia cardinal. mem_inertia_field_exactly:92–118 identifies the actual field automorphism as identity or the literal contact-root flip. The latter is not asserted to act trivially on the nonreduced entire branch fiber.

The six-source packet quantifies over all c, every i, and every field-valued R-point p satisfying the actual contact equation. Algebra over Q supplies the characteristic-zero convention; no supplied separable closure or residue embedding is needed for the argument.

## Canonical all-prime coverage

SourcePrimeValuationInertia318:19–37 equips Q.ResidueField with the actual Q[t] and Q structures, checks their scalar towers, and defines the canonical residuePoint. kernel_exact invokes Ideal.ker_algebraMap_residueField, so its kernel is the input Q, not merely a conjugate or isomorphic prime. Lines40–48 send the actual contact element hc to zero with those same structures. Lines50–60 specialize the previous embedded valuation construction, prove actual_prime=Q, and conclude cardinal two for its actual inertiaSubgroup.

Thus every prime Q of the original source order containing the literal finite contact polynomial is covered. The input is not a rational-point presentation. Nonzeroness follows through the earlier polynomial argument. The separate consumer's named endpoint is cardinal two; the six-source exact-element theorem can be specialized to the canonical point, but this review does not invent an additional theorem in the one-source packet.

## Evidence and limits

All target source hashes, application hashes, dependency pins and recorded successful module markers were checked. Working and frozen target source bytes agree. check105 has overall exit0 for SourceBranchValuation318; check110 has successful separate markers for PrimeLocalizationInertia318, SourceValuationInertia318 and the unchanged pinned Mathlib RamificationGroup. check112 has SourceOrderFieldEquiv318 exit0 before an older decomposition error. check113 has the final SourceValuationDecomposition318 exit0 before an older full-inertia error. check114 separately succeeds on the final SourceValuationFullInertia318. check116 succeeds on the canonical-prime source. These mixed logs are not described as entirely successful batches. The exact recorded strict commands use debug.skipKernelTC=false; their source/output bindings are retained as producer evidence, not independently replayed.

Combined recursive audit and integrated hosted replay remain pending for both packets. This read accepts the source-level application at that recorded validation status. It does not turn a pending recursive audit into a pass. The official RamificationGroup source was compiled from the pinned installed Mathlib source into an isolated overlay; no relaxed pin is consumed.

The result is valuation-theoretic inertia of order two at every original prime over each of the four finite contacts. No ramification-index equality, infinity inertia, nonreduced fiber identity, unrestricted projective automorphism classification, Jacobian/Picard construction, norm correspondence, polarization, PEL identification, or final arithmetic theorem follows from this acceptance.
