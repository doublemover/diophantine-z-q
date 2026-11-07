# Actual two-chart short-Weierstrass scheme

Four modules construct actual coordinate rings, actual scheme morphisms, and an actual glued scheme. No chart, overlap, smoothness, or section existence is supplied as a premise.

- `InfinityChart318`: the actual Y=1 quotient ring for z−x³−Axz²−Bz³; its explicit z-Jacobian; the genuinely smooth Jacobian localization; the actual closed section [0:1:0]; universal coordinate-map and extensionality lemmas.
- `WeierstrassOverlap318`: actual localization rings D(y) of the finite chart and D(z) of the infinity chart. The explicitly inverse algebra maps are (x,y)↦(x/y,1/y) and (x,z)↦(x/z,1/z). The proof works over every commutative ring, including zero divisors, using localization inverses rather than field division. `overlapEquiv` is the exact resulting R-algebra equivalence.
- `InfinitySmooth318`: the actual D(z) overlap and the explicit Jacobian open cover the entire infinity chart. Thus the whole Y=1 chart is smooth whenever the short-Weierstrass discriminant is a unit. The actual point at infinity is a closed section on this whole chart.
- `WeierstrassGluing318`: actual Scheme pushout of the two open-immersion overlap maps; actual finite and infinity open charts; coverage of every point; exact common base morphism; genuine smoothness; actual global section at infinity. The literal family over `OpenJModel318.Base N` has an unconditional smooth structure morphism and the specified section, using the already proved literal discriminant unit.

## Exact boundary

This is an actual two-chart cubic scheme, not a placeholder Scheme structure. The packet does not yet prove its identification with the homogeneous projective cubic, properness or separatedness, the group-scheme law, multiplication morphisms, or the relative primitive-torsion scheme. In particular the global section is not claimed to be a closed immersion merely from its closedness in the infinity chart. Those statements require further proofs. The source global refined geometric realization is still unproved.

## Reproduction

Run `bash infinity-elliptic-scheme/build.sh` from the common project root. It strictly rebuilds these four modules against the existing checked affine/model and Mathlib dependency cache, then recursively checks every declaration originating in these modules. It is not a fresh rebuild of all imported dependencies. The only allowed axiom roots are propext, Classical.choice, and Quot.sound.
