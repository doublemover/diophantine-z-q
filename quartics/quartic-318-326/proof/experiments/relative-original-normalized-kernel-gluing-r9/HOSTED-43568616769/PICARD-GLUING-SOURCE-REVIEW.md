# Independent original coefficient tensor source review

No source-level blocker found in the exact reviewed state. This is source/provenance review only, not a hosted candidate pass, kernel acceptance, whole-packet acceptance or declaration audit. No local Lean/Lake or user computer was used. Successor metadata/propagation requires its own review.

## Observed hidden-map failure
The exact own log rejects the hidden-f Algebra R S and oldRing-to-newRing instance registrations, then records their dependent scalar/pushout/linear cascades. Candidate replaces them with named exposed definitions and scopes their exact values explicitly in pushout and the affected result types/proofs. This changes public type text; no claim of byte-identical telescopes is appropriate. The intended k,R,S,B,f,N explicit arguments remain the same, and no additional caller premise is introduced.

## Actual actions and coherence
coefficientAlgebra is exactly f.toAlgebra. coefficientTower is the original f.commutes proof under that very action. chartAlgebra is exactly RelativeCoefficientChange.ringMap.hom.toAlgebra; the producer ringMap is native TensorProduct.map f (AlgHom.id k B). Thus the full original B factor is fixed while coefficients move by f. The existing rightAlgebra on S tensor_R oldRing and the Module R N compHom through algebraMap R oldRing are unchanged.

ringEquivalence is still native cancelBaseChange k R S S B, fixing S and mapping the original old chart through the displayed ringMap. rightEquivalence still uses its SAME additive map and proves oldRing linearity via multiplication by (1 tensor t) and ringEquivalence_right, rather than introducing an arbitrary linear comparison. tensorTransport preserves that oldRing balancing and the independent S action; tensorEquivalence then uses the same TensorPushoutModule.equivalence. No flatness, freeness, domain, basis or line-trivialization hypothesis is added.

## Categorical extension and consumers
categoricalEquivalence retains extension along the precise original ringMap.hom, restriction through algebraMap S newRing, and the native ScalarExtensionTensor.tensorEquiv. Its inverse pure-tensor theorem still sends s tensor n to (s tensor 1_B) tensor n under exactly that ring map. OriginalCoefficientSections composes this inverse with the actual chart-line sections comparison to obtain coefficient-only base change on the entire original affine chart. OriginalCoefficientTensorSection likewise consumes the same ringEquivalence and its old-chart restriction.

The downstream OriginalCoefficientSections source still contains its own hidden-f local registration and is not claimed to elaborate. The unchanged tmul simplification, hierarchy conversions in rightEquivalence, and concrete scalar coherence must be tested by hosted Lean. The named exposed bodies make the intended definitional comparison available, but source review is not evidence that the compiler completes it. No cap/trust/import change was made.

## Exact bindings

- OriginalCoefficientTensor318.lean: before `d843b9ef173be8bab7345dcca8845da9f29e6a1035745dea14541ce659938253`; reviewed `11fb3c77832f4fb3505cda99637666ac559cc800851e64f7be5b96b6697b59a0`.

The companion manifest binds own logs/RESULTs, Git-pinned predecessor intakes, and primary/consumer evidence. All pre-existing option lines are byte-identical.
