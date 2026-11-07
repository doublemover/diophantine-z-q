# Actual global relative normalization from finite normal affine pieces

This packet uses Mathlib's genuine Scheme.Hom.normalization: the actual scheme glued from the actual integral closures of the target affine-section rings in the source preimage-section rings. It does not introduce a substitute structure called a normalization.

The first theorem proves its actual structure morphism is finite from finiteness of the actual integral-closure rings on an actual affine cover of the target. The proof identifies the normalization's genuine affine opens and base morphisms, transfers the finite Spec maps through their actual scheme isomorphisms, and uses the proved target-locality criterion.

The source-facing theorem removes that finite-integral-closure premise. On each actual target affine chart it takes a normal Noetherian characteristic-zero section ring, a genuine denominator localization and a genuine finite smooth domain algebra of source sections compatible with the actual f.app map. The earlier concrete generic-field/trace-dual producer derives the finite integral closure. Consequently the actual global normalization morphism is finite. If the actual target is proper over a base, the constructed normalization is genuinely proper over that same base.

## Scope boundary

The actual source and target schemes, morphism, affine cover and local open-algebra identifications remain inputs. This does not construct the source arithmetic/PEL cover or assert an unbuilt projective target. The theorem concerns the actual normalization and its finite/proper structure map; it does not yet assert that the source-to-normalization map is an open immersion, since that additionally requires the actual source preimages to be affine and their local scheme identifications. Normalization source models, regular resolution and Arakelov data remain separate. No final geometric realization is claimed.

The pinned official Mathlib Normalization.lean dependency was freshly compiled with strict kernel checking, without modifying its source. Run `bash build.sh` to rebuild and recursively audit the four new theorem declarations.
