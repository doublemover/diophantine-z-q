# Original scalar inputs: finite-chart coordinate and embedding-square evaluation

Basis: run 43568616769 at e3d4f3341daf299c5658e7e9fe2f276f2e6aa58e. Descent predecessor forward-actual-two-descent-root-divisor-orders-r8, artifact 14104490080, ZIP SHA-256 4b0aa72245213e12424930789f768f52e691772c42b9d44d4f8b7491c5991c0e. ScalarPoleRealDomain318 now passes 4.075 s. First failure ScalarActualInputs318 takes 3.424 s. Its exact log/RESULT and before source are retained. Weighted propagation requires its own result and identical before bytes separately.

## Required and actual data

common_bounds quantifies every original integer h and concludes 0 ≤ ((chartU h)^2).re ≤ 1 and |normCoefficient (chartU h)| ≤ 1. The original chartU, quadratic field K, positive/negative real ring embeddings and normCoefficient remain unchanged. No substitute chart, real value, or sampled index is constructed. All public binders, other proofs, imports, resource settings and consumers are retained.

The source RealQuarticAmbient318.coordinate_bound covers every z in the original product of 16 real ovals, every i : Fin 8, and both embedding and coordinate indices : Fin 2. The actual argument is the same orbit of constant labels 1 at h, with membership supplied by orbit_mem. To obtain the original chartU h, the candidate writes its index as (0 : Fin 4).castAdd 4, definitionally the same 0 : Fin 8, and adds Fin.append_left to the simplification set. CoherentMultiplePrefix318.parameters appends the four label_j*h values before the four label_j*(h-1) values, so this exact left index evaluates to 1*h=h. Both real embeddings still use coordinate 0. No oval, chart subset, label choice, or domain hypothesis changes.

The third diagnostic leaves positiveEmbedding((chartU h)^2) and negativeEmbedding((chartU h)^2) rather than their image squares. The candidate first specializes map_pow to each exact original ring homomorphism, chartU h and exponent 2, then uses those literal equations while simplifying the original re_embedding((chartU h)^2).symm. This preserves the half-trace normalization (positive image + negative image)/2 and the same original rational real part. No unfolding of the quadratic-algebra lift or change of real scalar structure is used.

## Exact downstream identity and conditions

The unchanged square bounds and positivity reasoning use these two coordinate bounds and half-trace identity. The unchanged norm estimate still uses GeneratorScalarProgression318.embedding_product, so the resulting bounds are on the original normCoefficient and rational quadratic-field real part. The exact_mod_cast steps are unchanged. There are no new nonzero assumptions or excluded h values.

PreparedIntegerSource318.scalar_domain consumes common_bounds h for detector33 half-trace bounds and detector37 norm bounds, using the original DetectorGateWitness318.witness, original scalarB and the original pole_domain. Those consumer and producer definitions are copied as primary evidence. No pole equation or unrelated positive scalar is substituted.

## Verification scope

Before SHA-256 669eb03d31c5490f7278608a416e1e44ec64d10aa90c044c64c6636759e810f1; after dfb2085bb57eab66f47498bfed616a24367c85c373f5b652136d164e7e1701e1. Only three common_bounds normalization sites change. No source cap increase, accepted-snapshot promotion, local Lean/Lake, kernel acceptance or full arithmetic proof is claimed. Independent source and successor-propagation reviews are required; hosted elaboration remains pending.
