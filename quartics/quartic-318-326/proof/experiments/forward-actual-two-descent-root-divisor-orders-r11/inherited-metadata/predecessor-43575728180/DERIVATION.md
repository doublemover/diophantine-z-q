# ScalarActualInputs318: staged normalization of the original coordinates

## Observed scope and exact source

Hosted run 43572239136 at 52ab6e7faba5ec87dd4a1aa9d6cadcaef66aebca still stops at ScalarActualInputs318 in the descent r9 packet. Its own artifact 14104853228 binds the three residual mismatches at lines 29, 33 and 43. The previous castAdd / specialized-power simplifier route did not close them. The new route is reviewed anew; prior source approval is not Lean acceptance. Weighted r9 has its own artifact 14105372192 and requires independent byte/provenance comparison before propagation.

## Required input and original constructed object

RealQuarticAmbient318.coordinate_bound requires an actual z in its original product of sixteen real quartic ovals, indexed by all (Fin 8 × Fin 2 × Fin 2). Both applications retain z = orbit (fun _ => 1) h and its orbit_mem proof. The selected index is the original first left coordinate ((0 : Fin 4).castAdd 4), embedding indices 0 and 1, coordinate 0. This castAdd value is definitionally the original Fin 8 zero, not a new chart or a restricted orbit.

CoherentMultiplePrefix318.parameters is literally Fin.append (fun j => n j*h) (fun j => n j*(h-1)). The candidate first proves the exact parameter value at the typed castAdd index using Fin.append_left and one_mul. Each coordinate_bound proof is then changed to its actual positive/negative ring embedding applied to chartU of that same parameters value, before rewriting the established equality. This deliberately prevents broad simp from reducing castAdd to zero before the append lemma can match. No definition or instance is replaced.

## Exact scalar and power maps

RealDetectorRatios318.re_embedding is the original half-trace identity for every a : ConcreteG8Domain.K, using RealQuarticAmbient318.embedding. At a = (chartU h)^2 the candidate first changes its symmetric equality to the actual positiveEmbedding/negativeEmbedding of that square; only then are both ring-hom map_pow identities rewritten. The image, source square, real target squares, coefficient 1/2, rational-to-real cast and norm-product identity are unchanged. This staged route replaces the previous failed simultaneous simplification, not the embeddings themselves.

## Quantifiers, construction and consuming passage

The theorem remains common_bounds for every h : ℤ, including h = 0, without extra hypotheses. Both original embeddings are retained, and the rest of common_bounds (square bounds, real positivity, linarith, norm product and exact_mod_cast) is byte-identical. Its exact coefficient and norm bounds are consumed by PreparedIntegerSource318.scalar_domain at its call to common_bounds h; ScalarCompleteSource318 remains the unchanged source-completion dependency in that chain. detector33, detector37, detector118, preserved_slots and detector_root are unchanged; no fixed signed root, assignment slot, chart parameter, transition, scalar restriction or complete source gate is substituted.

The ordered predecessor closures remain 1299 and 1304 modules, respectively; only ScalarActualInputs318 changes. Each packet must retain its own RESULT, intake identity, artifact digest and before bytes. All imports and resource-option lines remain unchanged. No speculative ScalarCompleteSource318 or ScalarPolePreparation318 edits are included.

## Evidence and remaining obligations

Before SHA256: dfb2085bb57eab66f47498bfed616a24367c85c373f5b652136d164e7e1701e1.
Candidate SHA256: 3588513416aad80379722925395e0da45b22123081d73c545a5b86382690f097.
Primary sources retained: RealQuarticAmbient318, CoherentMultiplePrefix318, RealDetectorRatios318, GeneratorScalarProgression318 and downstream PreparedIntegerSource318 plus ScalarCompleteSource318. Exact source comparison and distinct independent application review are required. This is a source-level elaboration candidate, not a hosted Lean pass, recursive-axiom audit or proof of the full arithmetic theorem. No local Lean/Lake run was performed.
