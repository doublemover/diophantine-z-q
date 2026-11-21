# An arithmetic source for the original linear-q rectangle lower

This is the original 318/326 proof lane only. It does not assume a
GaussianKey or RectangleCounts to obtain positive prime mass. The new
native boundary works with an actual arithmetic Frobenius and ordinary
Mangoldt/Dirichlet objects. A genuine fixed-field affine prime estimate,
class field reciprocity, and the independent ambient A⁴ upper remain
outside the current Lean packets. All new source is uncompiled locally.

## Which actual indicator is counted

For fixed m (after the fixed Q and thin τ), write s=m², M=B₀·T_s
(the fixed even base times the new odd wheel product), F=2M. These are
not the archimedean B,N=B². Let K_M be the Gaussian ray field and
G=Gal(K_M/Q)=A_M⋊{1,c},
A_M=((Z[i]/M)^×)/im Z[i]^×. The labeled rational conjugacy subset C_s
is precisely the union of [r], [bar r] for positive integral References:
(9,0) mod16, (1,3) mod7, (0,1) at each other odd base prime, and both
translated norms units at every new wheel prime. Only residue units
occur. Its inverse image in the rational Galois group lies entirely
over the identity on Q(i). It has no inert or ramified primes. The
old 2M-conductor result gives K_M^ab=Q(ζ_F). See separate signed receipts
29e54194…, 3cd4198d… and EXACT-GAUSSIAN-ABELIAN-CONDUCTOR-AND-ORBIT.

ActualLinearQArtinSelector318.selected is this literal predicate on the
actual quotient, not a free assertion on an abstract type. It is
conjugation-stable. It equals existence of one norm-p Gaussian element
on that positive reference for any actual Gaussian prime generator
at a rational prime p coprime to M. The converse genuinely uses the
UFD: a norm-p element is prime, divides z·bar z=w·bar w, and hence is
associated to w or bar w by one global unit. The forward direction
uses the actual residue-unit quotient, then transport of the single
chosen representative. There is no independent sign at each factor.

The old external hFix is now rederived from the pinned native
Mathlib/RingTheory/Frobenius.lean b7bb6afc… . At an ideal Q of the actual
extension integer ring over (p), the Frobenius in arithFrobAt has
exponent Nat.card (Z/(p))=p, by Int.quotientSpanNatEquivZMod. Its
restriction to the embedded Gaussian subring is identity precisely on
the split subgroup A_M, as provided by the global ray class group
identification. Contract the power congruence to the literal ideal in
Z[i]. The earlier exact generator then has norm p. The one still
external geometric/arithmetic identification is that global Artin
reciprocity sends the actual principal generator class to this actual
native Frobenius in G. This is an equality, not an assumed norm-p
representation, not arithmetic Frobenius inverse, and not a statement
about simultaneously finding primes. Native isConj_arithFrobAt makes
same-rational-prime choices conjugate; old crossed-product orbit keeps
C_s fixed. Standard maximal-order CFT remains a named paper theorem.

## Exact finite conditional mean and ordinary model

For a unit b mod F, let d_s(b) count the actual elements of C_s projecting
to b under G→Gal(Q(ζ_F)/Q)=(Z/F)^×. For nonunits this count is 0.
The FT local model at conductor F is

    μ_s(b) = F·d_s(b)/|G|
           = (F/φ(F))·[d_s(b)/|G'|].

The bracket is the actual conditional probability, not a standalone
global density |C_s|/|G|. Marginalizing over a fibre kills precisely
group characters nontrivial on its kernel; finite subgroup translates
prove this directly. In particular this is not a diagonalization of
all nonabelian Frobenius classes by one-dimensional characters.
The mask for the unramified Frobenius is exact separately; the ordinary
comparison is only the scalar periodic factor d_s(b)/|G'| times ordinary
Λ, with the W-trick normalization φ(W)/W. For a unit b mod any fixed W
multiple of F, its W-tricked mean is φ(W)·η_{K,C_s}(b,W)
=d_s(b mod F)/|G'|. Extending by zero on nonunits is essential.

The ordinary twisted-model Fourier identity uses the actual pinned
PrimesInAP.lean ba0c50b9… L218, not an analytic estimate. For a unit
a mod F its residue-restricted Λ is the φ(F)^−1 sum of
χ(a^−1)χ(n)Λ(n). Summing weighted unit cells yields the exact periodic
model in ActualAffineOrdinaryDirichlet318. The pinned PrimesInAP
endpoint proves Dirichlet infinitude, not a fixed-field joint
Chebotarev-for-linear-forms prime-log asymptotic. Mathlib's
VonMangoldt cffb337f… supplies weight log p at p^e and its native
nonnegative log cap. ActualChebVonMangoldt318 explicitly uses the
tag at the prime BASE p, not the e-th power of Frobenius.

## Exact remaining quantitative statement, not an extra nonlinear search

With literal merged forms {q} ∪ {u+k Q²q} and fixed positive τ, at each
fixed s the unique external lower is the sum over finitely many tuples
of **genuine rational conjugacy classes** of the following statement:
Frei–Tinková v3, Theorem 1.4 with (1.9), (1.10), (1.15), dimension 2,
fixed K_M and each fixed tuple of classes C_i contained in C_s:

    Sum_{(u,q) in literal X_N cap Z²} ∏_i Λ_{K_M,C_i}(f_i(u,q))
      = (τ N²/8) · β_off(F) · E_{z mod F} ∏_i [F η_{K_M,C_i}(f_i(z),F)]
        + o_{K_M,tuple,c,τ}(N²).

Here X_N=[3N/4,7N/8]×[τN,2τN], all forms are positive there,
β_off(F)=∏_{p not dividing F}β_{Ψ,p}; gradients are pairwise
nonparallel by the exact two-form norm coordinates lemma. This is
the actual weighted diagonal over the same two integers, not independent
draws of each prime. The class tuple sum is a finite distributivity
identity in source, and total error is bounded by the finite sum of
errors with s fixed. It recovers precisely μ_s from the preceding
formula since Q(ζ_F) is contained in K_M. Relative "ordinary plus
residual" products have genuine higher correlations: on F₂,
f(x)=(-1)^x has zero marginal and f(u)f(q)f(u+q)=1. Thus zero-residue
means or character projection cannot supply the needed aggregate.
FT Prop 2.1 and Theorem 2.3 give the unconditional nilsequence inputs
for this joint linear theorem. Here "nonlinear" describes the
product/residual estimate, NOT the forms. No separate square-step
PET/Tao–Ziegler theorem is needed for this alternative.

The proper-power error is not hidden in the field estimate. A value
p^e≤N=B² with e≥2 lies in the explicit base/exponent box
p≤B, e≤Nat.log 2 (B²). For a contact form keep q as the free
coordinate; for the genuine q form keep u. The maps (value,free) are
injective. A power strip therefore has at most
(B+1)(1+log₂N)·O(N) keys, and contributes O_r(N^(3/2) log^(r+1)N) under
the actual nonnegative ∏log cap. After removing all r strips this is
o(N²) at every fixed m. The source proves the finite strip/card/weight
bound independently of FT. Ramified bases have tag none, not a second
set of counted primes.

## Same result at the original receiving type

The continued finite wheel calculation gives μ_s-average ≥c(Q,τ)/m
with one fixed positive c, through the exact off-minors line counts
and split/inert fibre losses. At the initial base conductor use u=q=b₀
unit; do not replace that residue by q=0. Thus for sufficiently large
N at fixed m we get genuine prime-log mass ≥A N²/m with A fixed
before m as in the existing paper. ActualLinearQFilteredRayMass318
forms exactly one finite set of (u,q) from the true-prime full-mask
product and produces the required RayRectangle from the per-prime
arithmetic receiver. Its primeRectangle_mass theorem identifies the
literal weighted sum without assuming the lower after selecting a key.
The ambient medium and large upper are then unchanged. No analytic
premise supplies a rank, elliptic point, h, Ready, or solution.

Primary links:
https://arxiv.org/html/2408.17441v3#S1.SS2
https://arxiv.org/html/2408.17441v3#S2.SS4
https://msp.org/ent/2025/4-1/ent-v4-n1-p.pdf
