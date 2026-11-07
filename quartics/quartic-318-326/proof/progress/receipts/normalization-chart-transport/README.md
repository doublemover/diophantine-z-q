# Actual proper integral extension of an open-j cover

Fresh strict replay passes 33 recursively audited declarations in three modules, with only propext, Classical.choice and Quot.sound. There are 13 public theorem/lemma declarations plus the actual transport constructions.

## Main endpoint

`ProperOpenJNormalization318.proper_integral_extension` starts with N≠0 and an actual domain B that is a finite etale algebra over the literal OpenJModel318.Base N. It constructs Mathlib's actual global relative normalization of the genuine map Spec B → P¹_Z and proves:

- the original Spec B embeds as an actual open subscheme;
- the constructed scheme is integral;
- its actual structure morphism to Spec Z is proper.

`normalization_finite` proves the map to the actual projective j-line finite. `normalization_dense` proves the original embedding injective with dense image. `normalization_over_Z` proves the exact diagram with the original canonical Z-structure of B.

No proper target, finite normalization, section-ring identification, finite closure or open source embedding is supplied in this endpoint. The target and both charts come from the frozen actual projective-j-line construction; the reciprocal chart uses the frozen actual localized-ring isomorphism and its exact source map.

## Actual chart transport

`IntegralClosureSquare318` constructs an actual integral-closure ring equivalence from a compatible pair of base/ambient ring isomorphisms, and proves module finiteness transports through it. `NormalizationChart318` constructs actual source/target section-ring isomorphisms for a genuine affine chart factorization and proves their exact commutative square. This discharges the real normalization section-ring interface, rather than substituting unrelated affine rings.

The two concrete normalization rings are finite by the previously checked trace-dual normal-model theorem, applied to the original and reciprocal coordinate maps separately. Their actual target opens cover P¹_Z, so the actual globally glued normalization is finite there. Properness then follows over the constructed proper P¹_Z.

## Remaining source boundary

The actual finite-etale algebra B and its domain/component are inputs: this does not construct the particular relative primitive-torsion modular cover or PEL model. The normal affine integral-closure rings are proved normal in the predecessor packets, but this packet does not add a global regular/semistable model, resolution, canonical-divisor identification or Arakelov comparison. Those actual source realizations remain separate. No unconditional GeometricRealization, FiveContact49Height, prime-pattern/converse theorem or complete integer-witness existence is inferred.
