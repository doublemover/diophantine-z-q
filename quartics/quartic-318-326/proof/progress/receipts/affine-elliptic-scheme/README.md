# Actual smooth affine elliptic family over the literal open j-line

This packet constructs an actual Mathlib Scheme and proves that its actual structure morphism is smooth. Its base is exactly OpenJModel318.Base N, the localization of Z[j] at 6N*j*(j−1728).

The coordinate ring is the literal quotient of R[X₀,X₁] by X₁²−X₀³−A X₀−B. For the source model, A=−3j/(j−1728) and B=−2j/(j−1728), using the actual unit inverse already defined in OpenJModel318. The quotient equation is proved in the coordinate ring. The actual Spec map is a closed immersion into the affine plane over the same base, and the base diagram commutes.

## Genuine smoothness producer

For a generic short Weierstrass equation, let fₓ=−3x²−A and fᵧ=2y. Inside the actual quotient ring the proof establishes the exact identity

Δ = 16*(6A x²−9B x+4A²)*fₓ − 8*(27B−18A x)*y*fᵧ,

where Δ=−16*(4A³+27B²). A unit discriminant therefore makes the two actual Jacobian minors span the unit ideal.

Each minor comes from the actual naive presentation. Composing it with the presentation of localization at that minor produces an actual submersive presentation: the composite Jacobian is the product of two copies of the now-invertible minor. Mathlib's locally-standard-smooth criterion gives actual smoothness of the quotient algebra. The Spec ring-hom property gives actual smoothness of the scheme morphism.

The literal OpenJModel discriminant is a unit by its proved denominator identities. Consequently the final structureMap_smooth instance has no discriminant, Jacobian, smoothness or local-chart premise. Every ring-base-changed coefficient model also has a smooth actual structure map.

## Exact boundary

This is the actual affine open of the family, with genuine scheme and smooth morphism structures. It is not a projective completion or a proper elliptic group scheme, and it does not construct a relative primitive-torsion scheme, a modular quotient, a Weil pairing or the final arithmetic cover. No global finite-etale or properness conclusion is inferred from this affine construction. Projective/infinity work is separate.

## Replay

`bash run.sh` strictly rebuilds four modules and recursively audits every declaration against only propext, Classical.choice and Quot.sound. No repository or Git files are changed.
