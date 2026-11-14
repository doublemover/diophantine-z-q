# Independent source review: FourRootActualGenericField318

Reviewer: /root/lean_review_resume, distinct from candidate author /root/pel_repair_resume.
Scope: internal model source/application comparison only. No local Lean/Lake execution. No kernel pass, full-proof acceptance, manuscript incorporation, or release acceptance is asserted.

## Frozen evidence

- Published baseline: a2d615a4183174328321ea21d60879add229de3a, run 43534276453.
- Exact observed packet: pel-original-zero-local-length-r33, artifact 14088657844.
- Predecessor intake SHA256 ca161ab070f07a67adc0ca058033ee4d714ae5a04a5878ef9473583dd4b9e7b9 matches RESULT.packet_sha256.
- Before source: 3522dee8f74dbf4f3b78af2e74c94d84c5e52fa813ed372e7b556dafaf72e4ac.
- Candidate source: b6d108947cec8ec4045f2354ba665b764d905dfb1571414a53c68cfee7365844.
- GENERIC_FIELD_APPLICATION.md: 2a43713ea4897f50fac1b1f5732b24782f62ef0e083128642765b44ff5a7a63b.
- Exact failure log: 1638cf957b584aa6da21a656a6584a02d81ec783724b934c7832a1b9ee17297d.

I read the actual before/after/diff, exact hosted errors, application comparison, source KummerTensorField318 and LinearContactSquareclass318, SourceKummerField318.independent_of_products, and actual downstream affine-domain/degree/independence consumers. The before bytes match all four current occurrences in zero-r33, cotangent-r39, character-r6, and trace-r6. This establishes copy identity, not a hosted observation for each packet.

The exact observed failure has unknown hb in product_nonsquare/independent, then applications of hb to erroneously hb-free declarations. RESULT shows the preceding affine coordinate ring and tensor presentation passed, and this module failed in 3.974 seconds. Those are hosted facts about the predecessor, not passes for this candidate.

## Application and assumption comparison

1. The intended source family has b : Fin 4 -> complex numbers and branch distinctness hb : Function.Injective b. LinearContactSquareclass318.twisted_product_nonsquare requires exactly this distinctness, every nonempty Finset (Fin 4), and a nonzero scalar twist. The unchanged proof supplies each nonempty subset, twist 1, one_ne_zero, and the same X-C(b k) radicands in RatFunc complex numbers. It does not restrict to singleton/pair products or discard a branch.
2. SourceKummerField318.independent_of_products requires nonsquareness for every nonempty subset; its actual proof enumerates all 15 nonempty four-index subsets. The repaired product_nonsquare b hb supplies precisely that family. No extra independence premise is introduced.
3. KummerTensorField318.actual_field/actual_degree require Fact of this exact QuadraticTower independence. Each repaired theorem constructs its own local Fact from independent b hb. Removing the file-wide instance eliminates hidden hb inference, without changing the argument or selecting a field factor.
4. Raw is the same entire fourfold tensor algebra of the four RootRing factors over RatFunc complex numbers. Degree remains 16 over the original polynomial-coordinate fraction field. genericFiber is still the same baseChange equivalence. TensorRing, finite-free structure, includeRight embedding, and its injectivity are unchanged.
5. tensor_domain still transfers the field domain through the same embedding. affine_domain still transfers through the literal original affine polynomial-quotient equivalence. Neither is a theorem about a substituted carrier, generic component, shifted coordinate, or different normalization.
6. The six theorem headers intentionally acquire the explicit original hb argument. Literal Lean signatures therefore change; the repair restores the intended section hypothesis and existing consumer calling convention. The invalid hb-free field assertions were not accepted mathematical statements. genericFiber, embedding, embedding_injective, affineEmbedding and affineEmbedding_injective remain hb-free and byte-identical. No imports, options, trust settings or resource budgets change.
7. Actual downstream consumers already use affine_domain b hb, independent b hb and actual_degree b hb, while the embedding consumers remain hb-free. I read FourRootAffineSmooth318.integrallyClosed and FourRootActualOrderGalois318's exact domain, integral-closure and degree uses, plus searched the current zero packet's domain consumers. Their resulting objects/maps are not replaced. Later independent scope/elaboration failures in unchanged consumers remain possible and are not covered by this source review.

## Conclusion and limits

No source-level blocker found in this bounded binder/local-instance repair. It is suitable for exact-copy successor propagation and hosted testing, not proof acceptance. Candidate Lean elaboration/kernel checking remains pending. Existing historical failures, unrelated source bytes and acceptance records must be preserved. A later propagation review must bind each successor's own exact predecessor result, full file order, source hashes and all ancillary changed/reused/unchanged classifications to actual bytes.
