# Both original sieve pairs after the actual lattice substitution

All280 predecessor sources remain byte-identical. This successor joins rational coprimality to the actual integer lattice-basis substitution rather than assuming an arbitrary invertible coordinate replacement.

LiteralPolynomialBasisEquiv318 defines the exact rational triangular substitution x->rX,z->ArX+qZ,w->DrX+qrW. It constructs its polynomial inverse X->x/r,Z->(z-Ax)/q,W->(w-Dx)/(qr), checks BOTH compositions on the actual polynomial generators using explicit inverse-coefficient identities, and builds an algebra automorphism. Relative primality is transported using that actual inverse. The evaluation theorem identifies this polynomial map with the literal rational basis-coordinate formulas.

ActualSlicePolynomialPreparation318 specializes q,r to the finite/infinity products actually constructed from primeFactors(|t|) outside2κ. Positivity gives the needed rational nonzero denominators. Both previously constructed original rational pairs remain relatively prime after this same basis substitution, including the t=-2 exceptional second chart.

The integer content side remains tied to the same actual q,r,A,D basis. The earlier explicit residue inverse and nonzero K evaluation produce an integer point outside any proposed content prime p not dividingt. Crucially, the new replacement_pair_nonzero theorem uses K-D=P(P+2t²-2xz) to exclude common vanishing for the ACTUAL first replacement pair(P,D), not only(P,K). actual_pair_nonzero_value supplies witnesses for both selected pairs after the original integer lattice substitution. Thus both rational polynomial and integer content prerequisites are connected to the same original data.

These are the algebraic prerequisites for a quantitative geometric sieve, not a quantitative sieve theorem. No reduced-basis/minima distribution, coefficient-height estimate or weighted tail follows merely from this algebra automorphism. Originalκ, the literalR correction and all 2-adic exclusions remain unchanged. The polynomial map is a rational automorphism; its corresponding integer basis has the original indexM² and is NOT claimed unimodular overZ.

Validation:6 symbolic inverse-coordinate compositions,192 actual substituted rational pair gcds,180 explicit witnesses for BOTH actual pairs, plus inherited original slice/code/index checks. Pinned primary AlgEquiv.ofAlgHom, comp_aeval_apply and actual relative-prime reflection APIs inspected. Static282/222 source-policy/dependency closure pass. No local Lean compile.

## Immutable r2 independent-review repair
The primary IsRelPrime.of_map theorem requires IsLocalHom of its map. r1 used the bare aeval backward hom, for which typeclass inference cannot see the proved inverse. r2 uses the actual previously CONSTRUCTED algebra equivalence's inverse, which carries the local-hom/unit-reflection instance. It simplifies exact inverse compositions to the original relative-primality theorem. No local-hom or invertibility hypothesis is added. All281 other sources remain byte-identical.
