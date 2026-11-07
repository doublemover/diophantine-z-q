# Independent review: actual global relative normalization

Accepted. The producer and exhaustive audit were copied verbatim and rebuilt under `-Ddebug.skipKernelTC=false`. All four declarations pass with only propext, Classical.choice and Quot.sound.

The construction is Mathlib's actual `Scheme.Hom.normalization`, not a parallel family of rings. The affine cover is an actual cover of the target, and the local algebra is the full integral closure of the actual target sections in actual sections of the preimage. The proof compares the genuine restricted normalization morphism with its actual affine Spec map, including the open-range identification and target chart isomorphism. Finiteness is then the target-local property, and properness follows from finiteness.

The stronger producer obtains local integral-closure finiteness from the reviewed finite smooth denominator-open theorem. Domain, characteristic-zero, Noetherian and normal target-section assumptions are explicit, as are domain and finite smooth source-section data, the nonzero denominators and the scalar-tower compatibility with the actual scheme map. It does not assume the desired global finite morphism or finite normalization pieces.

The final composition is proper over a further base only when the target map to that base is actually proper. This is not a construction of a projective target or compactification. Actual source/component/family realization, source open-immersion refinement, projective/arithmetic target construction, regular models and Arakelov identifications remain explicit. No semantic mismatch found.
