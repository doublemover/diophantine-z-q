# Independent review: fixed 673 operators and all actual parity weights

Signed: Vesper, independent mathematical reviewer, 2026-11-21.
Disposition: PASS for the exact fixed finite data; the moving product is not evaluated.

Both author manifests and papers were checksum verified:
- Fixed framed degree-17 and Frobenius transports: 102b3502bc86c1209e2b497688a4d753431475a934f7c4626a5c6b4a96680304 / 90accdc012f06ecf3c9c23cacb229f99e08bb8c568ad2338e2997aa849f77e80. Exact transport JSON 2745f5eceb36ad4d40b40e113433cf4da673893f107c538260f616c7d03fa4b1.
- Literal marked weights: e6f81e8c2cf0c5b84271a747c0a7ba1576885cfb307eb4337277836968297733 / 7d679417dea5717213f87bb85785004a9912db933202b18be44a4674ea6d07d0.

Both standalone standard-library replays independently regenerated their full published JSON byte for byte. I separately checked 120 packed field products against direct polynomial convolution, including the exact no-carry bound. The irreducible quadratic-subfield-to-degree-32 representation follows from the order of the defining element and the order of 673 modulo 1024. The exact Legendre Hasse factor product gives the complete 56 supersingular models, and the exact torsion tables certify bases by order and distinctness. The 18 degree-17 lines on each model use their actual kernels, quotient and four transported basis values, and the simultaneous sign after scale normalization is the precise geometric frame quotient. I checked the directed coordinate action, the degree-17 dual composition and Frobenius commutation checks. In the ramified characteristic slot the operator has one actual Frobenius row per model, not 674 étale lines. Thus the 1,008 degree-17 and 56 Frobenius rows describe the full action on the 344,064 rigid frame classes.

The weight table uses the order-16 function on the actual cyclic subgroup both before and after quotient by its actual 3-subgroup. I checked the two level degeneracies and the unique simultaneous lift in the concordant chart; the independent subgroup enumeration matches all 5,376 distinct chart labels. The exact ordered pair is needed, not just the source supersingular j. I additionally independently recomputed all 1,368 orbit weights directly from their long chart coordinates in a separate quadratic-pair arithmetic. The four-label orbit counts are 616 even and 704 odd weights; the two-label Frobenius-equals-Fricke counts are 24 and 24, and no labels are fixed individually by Frobenius. These are weights, not CM multiplicities of any selected discriminant or a computed aggregate.

This stage provides the two fixed operators and finite weight receiver at the helper; no remaining moving-prime operator, actual selected n or its supersingular product, fourth-pole construction, marked rational point, or rank is asserted.
