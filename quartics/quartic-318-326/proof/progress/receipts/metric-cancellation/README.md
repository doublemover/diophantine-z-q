# Exact metric cancellation and actual logarithmic weight

This packet has three Lean modules and 19 kernel-checked public theorems. It extends the finite five-contact metric packet. It does not prove the full five-contact height theorem or manufacture its geometric, modular, or Arakelov inputs.

## Checked interfaces

`MetricCancellation318` proves exact finite-embedding averaged cancellation with the common Wronskian weight k. The assumptions retain both actual point-height and Faltings/Wronskian inequalities. It verifies the GR normalization shift log(sqrt(pi)) < 1, the weight bound k <= d^2, the finite logarithmic budget, and the aggregation to 2^11*d^2*L^2. It also proves the complete retained geometric additive constant is less than 120, with the actual pi, 210, J, and Cmet constants.

`ModularVerticalAlgebra318` verifies the actual open-j-line elliptic model: 4a^3+27b^2=-108*1728*j^2/(j-1728)^3, its nonvanishing, and its exact j-invariant. This is the algebraic model input, not a Lean formalization of the entire finite-etale quotient argument.

`ActualLogWeight318` sets C=210^300 and binds the growth certificate to the actual L=log(6dN). From R>=1, d<2^14*C*R^(97/32), and N<=C*R^2, it proves L<4096+6logR<2^13*R^(1/32). Combined with the explicit Jacobian height input, it yields h<2^65*C^2*R^(49/8). The level/index and Jacobian inequalities remain visible premises.

## Fresh primary-source and application checks

1. Yuan, *Explicit Kodaira-Spencer map over Shimura Curves*, author English translation dated 30 April 2024, Theorem 1.1, printed page 3. The image is exactly d_B*omega_X^2 and the map is isometric. The Petersson cotangent norm is 2 Im(tau). His abelian-surface Hodge norm is pi^-1 times the original Faltings norm, so its height is shifted by +log(pi). The sublattice d_B*L has height h(L)-log(d_B), giving exactly the source's +log(210) term. The theorem and metric conventions were read and visually checked. The actual contact model, normalizer quotient, fiber-field degree, and all pullback identifications are still separate dependencies.
2. Javanpeykar's relevant original definitions/theorems were freshly checked in the preceding five-contact-metric packet. They give the exact Wronskian weight and minimal-model inequality used here. The same local coordinate at each embedding is essential for cancellation.
3. The source's open-j-line vertical-support argument is valid at the stated algebraic-geometric application scope: N-torsion is finite etale after inverting N, primitive points form a finite locally constant set, and its H-quotient is still such a set without requiring |H| invertible. Since -1 belongs to H, the automorphism/twist ambiguity disappears away from j=0,1728. The finite-etale cover is normal over the regular base, identifies with the normalization, and stays so after number-ring base change. The three Lean lemmas check its literal elliptic-model algebra only.
4. Rémond, *Propriétés de la hauteur de Faltings*, Corollary 1.2, original page 1, and the stable-height observation on page 2 were checked. There is no degree or polarization hypothesis in h(B)+h(A/B)<=h(A). Dimension-linear changes of normalization do not affect this inequality. The stated Bost constant in the original normalization is log(pi*sqrt(2)), consistent with the loose 3/2 budget.
5. Gaudron-Rémond, *Nouveaux théorèmes d'isogénie*, author version September 2022, section 1.5 and Theorem 1.9(1), printed page 15, were checked, including a rendered page. In dimension g, Xi(A)=((7g)^(8g^2)*[K:Q]*max(1,log[K:Q],h_F(A)))^(2g^2). Isogenous A and B admit maps in both directions of degree at most Xi(A)^2, with no polarization assumption. At g=2 this gives precisely the source's half-log expression. The current arithmetic.md bibliography calls the linked document by a different older title; the linked theorem itself is the correct input.

The retained level/conductor source chain was read, but this packet does not claim a fresh primary-source validation of every modularity, local conductor, compatible-system, or morphism producer. The modular curve, non-Weierstrass choice, embedded cusp disc, actual differential/orthogonality estimate, and global Arakelov inequalities must still be supplied. No full five-contact theorem is asserted by this packet.

## Reproduction and freezing

Run `./build.sh`. All 19 public theorems use kernel checking with `-Ddebug.skipKernelTC=false`. Their only axiom roots are propext, Classical.choice, and Quot.sound. `receipt.json` records hashes and external source URLs. PDF/text/screenshots are verification inputs, not necessary to vendor with the Lean checkpoint. The packet was developed outside the repository and makes no Git changes.
