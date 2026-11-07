# Actual finite normal affine model of a connected open j-cover

This packet strengthens the earlier integral affine model at a genuine finite smooth connected-cover input. The final literal theorem assumes N≠0 and an actual domain B finite etale over OpenJModel318.Base N, with its compatible Z[j]-algebra structure. It concludes that the actual integral closure of Z[j] in B is finite, integrally closed and Noetherian. Its actual Spec structure morphism is finite and proper over the affine integral j-line. The original denominator-open scheme isomorphism is supplied by the unchanged affine-integral-model packet.

## Derived arithmetic and geometric inputs

1. For a finite smooth domain algebra B over a normal domain A, the actual generic tensor fiber B⊗Frac(A) is a domain by localization and flatness. It is finite dimensional, so an actual field structure is constructed.
2. The smooth integral-closure base-change theorem proves B is the integral closure in that genuine generic fiber. It follows that B is integrally closed. The generic field is proved to be the actual fraction field of B, with no supplied generic-field identification.
3. For the unlocalized base R, the actual integral closure of R inside B is also the integral closure of R in this constructed field. Characteristic zero supplies separability. Mathlib's proved trace-dual argument over a normal Noetherian base makes this integral closure finite. Its normality and Noetherianity follow.
4. Localization normality and the fraction-field algebra maps are constructed from d≠0; they are not extra input certificates. The source denominator 6N*j*(j−1728) is proved nonzero from N≠0. Z[j] supplies the normal Noetherian characteristic-zero base instances.

No normality of B, generic field, finite-dimensionality, separability, finite normalization or local DVR structure is supplied to the final source theorem.

## Exact retained boundary

B must still be an actual domain and finite etale open-cover algebra. This is the connected/domain version; it does not assert every possibly disconnected finite etale algebra is a domain, and it does not identify a chosen component of a source cover. The packet does not construct relative primitive torsion, the actual arithmetic/PEL cover, projective compactification of the j-line, its curve model or regular resolution, or global Arakelov data. Properness is over the affine base only. No final geometric-realization or five-contact theorem is asserted.

## Replay

Run `bash build.sh`. Four source modules are freshly strictly kernel-rebuilt and all 25 declarations recursively audited against only propext, Classical.choice and Quot.sound. No repository/Git/Mathlib source modifications.
