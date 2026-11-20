# One fixed ternary theta coefficient for the direct CM4 test

This concerns the proven direct low-level Hilbert trace and its four finite calibrations, not the older signed four-coefficient test. It specifies a single universal modular form with the required coefficients. It does not evaluate a production coefficient or furnish a prime-ray nonvanishing theorem.

## Fixed lattices and fixed coefficient functional

Take the 416 marked labels x at 53 of the pinned level-48 chart. Let M_x be the corresponding maximal quaternion order of the **source** elliptic curve, in the five actual q29 frames. Let L_x={ξ∈M_x : tr(ξ)=0} with Q(ξ)=nrd(ξ), an integral positive definite ternary quadratic form. Choose the fixed integer lift λ_x∈{0,…,12} of the actual order-13 projection of the based chart f(x). In computing a reduced direct CM4 embedding put ξ=α−2: then α has trace 4 and norm 4(d+1), and Q(ξ)=4d. Conversely such ξ gives α=2+ξ with this trace and norm, and α defines the distinguished generator 4ω₀ of the conductor-four order. No weighting by a real or imaginary genus character is used.

Set N=lcm(64,3,53)=10176. Define S_x⊂L_x/N L_x by these fixed local predicates:

1. The endomorphism α=2+ξ is nonzero modulo 2 of the source matrix ring, and on the actual marked cyclic 16 line acts as λ₁₆=4 when Q(ξ)≡12 mod64, or λ₁₆=12 when Q(ξ)≡44 mod64. Other norm residues are discarded.
2. On the actual marked cyclic 3 line α acts as 1.
3. The coefficient of J in the polarized reduction of 2ξ at 53 is in {1,…,26} (choose its representative modulo 53). The two permitted nonzero polarizations for every eligible d differ by sign, so this fixes the same one orientation as the calibration without knowing d mod53 independently.

The rule in (1) is the literal choice of ω₀=u+vω used in the calibration: d≡11 mod24 implies d≡3 or 11 mod16; the lexicographically first (u,v) modulo4 is (0,3) or (2,3) respectively, and the eigenvalue is 4(u−v) modulo16. Congruence of ξ modulo N implies congruence of its quadratic norm modulo 64 by integrality of the polar form, and congruence of all matrix/tangent readings modulo the stated moduli. Thus these are truly fixed finite coset predicates, not dependent on factoring θ or on adapting the rule to a successful trace. They can be kept in these symbolic CRT tests; the construction does not materialize N³ entries.

Define the fixed formal series
~~~
Θ(Q) = Σ_{x} λ_x Σ_{μ∈S_x} Σ_{ξ∈N L_x+μ} Q^{nrd(ξ)} .
~~~
For eligible positive squarefree d with d≡11 mod24 and −d nonsquare at 53, the fine separate source and target conductor (4,4), exact 16 and 3 eigenline restrictions, and chosen residue orientation are precisely the ones already proved in the direct calibration. Away from 2 the local maximal CM order acts automatically because 4 is a unit there. In particular the single coefficient satisfies
~~~
[Q^{4d}] Θ(Q) mod13 = Σ_{a∈Pic(O₄)} [224]f(P_a) coordinate
                     = 2 Λ_d .
~~~
This is equality of the oriented finite sums in order-13 coordinates, with repeated actual markings counted with their correct multiplicity. The previous q29 j=0 convention (one representative of each geometric mark orbit) applies unchanged. The θ used in d₁ changes the coefficient address, not this operator.

## Modularity and exact lattice datum

Each theta summand is a discriminant-group component for the positive definite even lattice N L_x: the norm polar form B is integral with B(ξ,ξ)=2Q(ξ) even, and the shift μ∈L_x lies in (N L_x)^∨. By the standard lattice theta transformation (e.g. [Borcherds, Automorphic forms with singularities on Grassmannians, §4](https://arxiv.org/abs/alg-geom/9609022)), its vector of all discriminant coset sums transforms in weight 3/2 for the associated Weil representation. Therefore the fixed linear combination is a scalar form on their common kernel in the metaplectic group. No small Γ₀ space, Kohnen plus projection, eigenform identification, cusp assertion, or Sturm-derived prime coefficient law is being imported.

The exact trace-zero lattices satisfy polar determinant 2·53² and level 212. One can compute them from the frozen HNF bases without a change to the q29 integral geometry. If h₀,…,h₃ are the four HNF basis columns, tr(h₀)=2 and tr(h₁) is odd. Then k=((1−tr(h₁))/2)h₀+h₁ has trace one, and h_i−tr(h_i)k for i=0,2,3 are a unimodular kernel basis. For each basis the checker writes the exact Gram matrix and the smallest L making L times its inverse integral with even diagonal. Hence after dilation by N the even lattices have level exactly 212N²=21,952,806,912. This is the Weil lattice level, not a claim of a minimal scalar automorphic conductor. The checker also verifies the universal predicates on the 24 exact chosen d=323 rows and the local eigenvalue rule in all four numerical controls.

## The remaining production problem

Write d₀=Rq and d₁=Rθq where R=β·114649 on the proven one-I ray. A joint nonzero statement for the two addresses 4Rq,4Rθq of this one fixed series would suffice, together with the full arithmetic selection. Equivalently the two U-reindexed coefficient series could be studied at the same prime q (this is coefficient reindexing, not a local \(T(q^2)\) relation). Weight-3/2 Hecke recurrences at unramified q move between indices with the **same** squarefree part and do not themselves control the new prime-cofactor addresses. A proving algorithm merely iterating through all norms to either index also does not help. What is still unavailable is a certified fast coefficient extraction for this explicit functional at the true large addresses, or a same-ray prime-cofactor nonvanishing theorem for both. The compact coset identity supplies neither a numerical production ray nor mod-13 information at it.

~~~sh
python3 -B check_trace_zero_cosets.py | cmp - EXACT-FIXED-TRACE-ZERO-LATTICES.json
~~~
Explicit --book and --calibration options support a relocated source tree.
