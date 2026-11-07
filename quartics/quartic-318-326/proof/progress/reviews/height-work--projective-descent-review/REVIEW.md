# Independent projective and homogeneous descent review

Accepted at the stated scope after a fresh copied-source strict kernel rebuild and exhaustive declaration audits: 12 declarations in ProjectiveGalois318 and 4 in HomogeneousGalois318. Both copied mathematical sources match the frozen producers byte for byte. Only propext, Classical.choice and Quot.sound occur.

## Mathematical checks

- Projective invariance is converted through Mathlib's actual projectivization equivalence relation to a nonzero scalar multiple, with the orientation used consistently. Normalizing a nonzero coordinate cancels that scalar, so every coordinate ratio is fixed. The actual finite-Galois fixed-field theorem then supplies base-field coordinates; the selected coordinate is one and proves the descended vector is nonzero.
- The actual projective base-change map is injective on coordinate vectors and the resulting projective equality is proved in Mathlib's quotient. No genus-zero splitting, rational ratio or rationality premise is assumed.
- The five-label specialization uses the independently proved injectivity of the literal inertia labels. A label-preserving Galois permutation fixes each point, after which the general projective theorem applies.
- Homogeneous scaling is derived monomial by monomial from actual degree support. It works for any degree, including zero, and any family of equations. Field-map injectivity then descends the original homogeneous equations. The final theorem supplies both actual base-change equality and vanishing equations, rather than assuming descended curve membership.

## Retained geometric boundary

The finite Galois extension, the actual canonical curve and its base-field projective embedding/equations, the five branch points and their Galois/inertia compatibility remain input. These theorems do not construct those data or prove a genus-zero curve split without a descended point.

The replay uses review-folder-first imports; the homogeneous module consumes the freshly rebuilt copied projective module. It is not a fresh replay of all Mathlib or inertia-label dependencies.
