# Independent source review: Picard gluing successor

Internal source review only. No local Lean/Lake/compiler/proof build was run. No candidate kernel pass or independent mathematical acceptance is claimed.

Base b3d76fb41c03f9194b0613eac0a9b4cb04b2576c; hosted run 43564923898. Before source and intake were byte-compared against the published Git object. The own RESULT packet hash matches that intake.

- Predecessor: relative-original-normalized-kernel-gluing-r7.
- Candidate: relative-original-normalized-kernel-gluing-r8, RelativeCoefficientFunctor318.lean.
- Before SHA-256: 625183964e39b5205ca4bfb1c0948da45d1162968d1abe2c85ee907ebb118860.
- After SHA-256: fcbdfa493e4dd423efe0d3d2308a9acb2313be001350f587ecf1fed9d37b4092.
- Own RESULT SHA-256: 04a052b92202ee6123f24fe0bc485b0ca2c10e2b38fb06f3939b0f336e7ea8ba.
- Exact log SHA-256: 33cd9e7fe3f5185fed05ebf10e2ac2e7ae686926693ea23e01140613b2013885.

## Exact diagnostic and change

The two observed errors are pure-tensor branches of ring_identity and ring_composition. After category/ring-hom extensionality, the goals contain CommRingCat.Hom.hom(ringMap ...), so ringMap_tmul is an unused simplification argument. The candidate changes only those two simp lists to unfold the exposed original ringMap definition.

The unchanged definition is CommRingCat.ofHom of the toRingHom of Algebra.TensorProduct.map f (AlgHom.id k B). Unfolding therefore exposes exactly the same native tensor map beneath the displayed categorical hom projection; it does not replace it with a pointwise surrogate. On every pure tensor r tensor b the identity case is r tensor b and the composition case is g(f r) tensor b on both sides. Both additive induction branches remain unchanged and extend this equality to the entire tensor ring. The current TensorProduct.inductionOn used here has the tmul/add eliminator already accepted in the producer; no missing zero or coefficient premise is introduced.

The required domain remains arbitrary commutative rings k,R,S,T,B with their original k-algebras and arbitrary k-algebra homs f,g. The B factor remains fixed by the identity, not an independently selected action. Composition is still ringMap(f) followed by ringMap(g) = ringMap(g.comp f); the contravariant Spec/family direction is not reversed. No localization, restricted locus, scalar/Euler factor, or exceptional index is changed.

I read the producer's ringMap, ringMap_tmul, original_square, coefficient_square and edge_square. The already-hosted producer edge_square uses the identical native unfolding strategy on both tensor factors. I also checked the immediate consumer ContactCoefficientWholeOpens: it imports this module and consumes the unchanged family_identity/family_composition for the same p-first families. Search of this packet finds no direct consumer of the two changed ring lemmas; the family-map proofs remain separate and byte-unchanged, so a direct mathematical dependency is not being invented.

The own RESULT records ContactRelativeWholeOpenSections passing 16.652s and RelativeCoefficientFunctor failing 2.369s. This does not establish a candidate pass. Only this root differs in the 1,298-source closure. All public statements, maps, hypotheses and options remain unchanged. No source-level blocker found; successful simplification/elaboration remains to be tested by hosted CI.

Final packet contract/provenance binding is a separate review. Source-only clearance does not authorize changed sources or publication.
