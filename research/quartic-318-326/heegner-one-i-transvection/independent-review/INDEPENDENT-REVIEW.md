# Independent review: all-good transvection image test and finite-space density

Bound to exact image note 8ef84255dc8ea0b8482489d9345c16b8fb418cd2badd1f248e8736cfddccad77,
manifest 9846bf75c738b57f3967da701ba073405948d6465665ea5f4befa2bccd51e2f4;
and joint density note 35482911e17208732b1fed3386bd3b22ce06482983e4b721433e738f13136380,
manifest bd8d9d5d4008c23f6f0a986d27101484f65de17fb0806430681efe67236b9ee5.
Author incidence, actual-53, and finite-count outputs reproduced byte for byte.

The Weil embedding uses the determinant action on μ. Transport of
Shapiro evaluation at P by σ yields evaluation at σP modulo a boundary,
so scaling by [a] gives λ=a, not its inverse. The incidence sum has the
literal 13 points c(v)=1, without dividing by 13. Its projective matrix
c(v)^11 has rank 12 by degree-eleven monomial interpolation modulo 13;
linear forms give the exact kernel. The bare transpose pairs opposite
homogeneities and its kernel is the covector-linear submodule V, giving
cokernel V* before the determinant twist, and the original V after it.
No invariants in the image/cokernel give the exact cohomology statements.
The degree-13 compositum and unaveraged sum identify the right map with
the ordinary Kummer norm on the same incident pair. The quotient Q=M/V
is absolutely simple: distinct torus weights allow monomial projections,
and the two shears give a pure power and then every monomial.

In a transvection u, the 13-cycle on moving labels contributes a
rank-one norm N_u, zero on the fixed label and zero on actual V.
On a moving nonzero point the local Frobenius is g^13, not g.
In the finite affine extension, variation of the lift by w changes
the 13th-power value by N_u w. If the kernel image W₀ is not contained
in V, irreducibility makes some such variation nonzero. Conjugation
of these powers (linear image identity) preserves the nonzero property,
and Chebotarev gives a good prime witnessing it. For a true V cocycle,
N_u=0 on V gives necessity. If W₀⊂V, the quotient class inflates from
finite H¹(G,Q); this is zero because H¹(G,M)=0 (point Shapiro,
d² on Hom(U,μ) and order-12 quotient prime-to-13) and H²(G,V)=0
(the central -I subgroup has zero invariants and vanishing higher
cohomology). The last ordinary condition is the true local formal
V⁺ line: the unramified V⁻ character −2 has no invariants, and at the
actual w+ of degree 12 restriction into its test is injective by
transfer. Good primes away from 13 are unramified by the S condition
and joint point evaluations; the previous bad-place zero classes
are unchanged.

I independently computed in F_(53^13) with explicit polynomial
multiplication/reduction and binary point multiplication, checking
that the chosen factor divides the true x-polynomial, is irreducible,
and the chosen sign gives a point of exact order 13. The curve has
52 points over F53, so the repeated Frobenius eigenvalue 1 cannot be
scalar. The projected residue scores for v, 1+W, and 2+W are 0,0,8.
This last value is a local canary, not a globally admissible S-class.
The replay accepts the exact point-field and transvection-53 JSONs.

For a prescribed finite candidate space, proper projected kernel
image in Q^m would be annihilated by a nonzero map to Q, because a
direct sum of simple modules is semisimple even in defining
characteristic. Absolute simplicity gives End_G(Q)=F13; the
annihilation would yield a forbidden linear relation by the same
finite inflation vanishing. Thus the transvection norm ranges
uniformly over all F13^m scores on the lifts. Conjugacy and the choice
of moving point or Weil-root generator affect all coordinates by the
same nonzero scalar. Chebotarev yields relative density 13^(-m)
for the zero row and 12·13^(-m) for each specified nonzero projective
direction. Independently the transvection class has size
26208/(13·12)=168, yielding absolute density 1/169 for rejection of
one false candidate. This proves existence of determining rows for
an already prescribed finite candidate space, not an explicit
numerical cutoff, certified basis, class/Selmer rank or rational point.

Independent reviewer: Vesper (high_review_ci), 2026-11-21 UTC.
