# Actual open-and-closed finite kernel component

The exact original rank-eight map into the actual global literal tripling fiber is now proved to be both an open and a closed immersion.

- `LiteralKernelOpenClosed318.isPullback` identifies the actual finite-fiber map as the finite-chart base change.
- `canonical_eq` identifies the previously frozen canonical rank-eight map with the actual finite-fiber isomorphism followed by that base change.
- `canonical_open_closed` gives both immersion properties for that exact map.
- `LiteralKernelFiniteRange318.canonical_range` identifies its exact image as the inverse image of the entire finite curve chart under the actual global kernel projection.
- `LiteralKernelComplement318.complement` is the genuine complementary open subscheme; `iso` gives the actual coproduct decomposition of the global kernel into the original rank-eight scheme and this complement. The two coproduct restriction identities are explicit.

The complement is NOT yet identified with the base or zero section by this packet. In particular, this is not a rank-nine finite-etale kernel theorem. Its zero-neighborhood interpretation is the next independent geometric input.

Three sources passed strict checks, and their recursive audit passed 68 declarations with only propext, Classical.choice and Quot.sound. No local full-chain replay. Hosted integration and independent review remain separate.
