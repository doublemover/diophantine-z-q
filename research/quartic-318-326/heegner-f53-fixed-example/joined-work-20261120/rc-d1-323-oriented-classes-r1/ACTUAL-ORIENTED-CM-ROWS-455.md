# The literal oriented CM seed and 20 horizontal class paths

Fixed test only: selected arithmetic d=323, K=Q(sqrt(−455)),
N=5,007,792, residue characteristic 53, u²=22 in F53², and the
same level root β=60875 modulo 2N. No modular values, class sum
nonvanishing, analytic rank, or proof for arbitrary selected d is
asserted here.

## Seed and exact cyclic orientation

On A:y²=x³+1 over F53² put F=(x^53,y^53); the cubic is a permutation
of F53, so a53(A)=0 and F²=[−53]. For ζ=(-1−u/9)/2, put
ω(x,y)=(ζx,y), J=1+2ω, V=(1+ω)F. We have
(u/9)²=−3, ζ²+ζ+1=0, Fω=ω²F, so J²=−3,
V²=−53 and JV=−VJ. The exact operators
α=−9J−2V and Ω=−4−9ω−V satisfy α²=−455,
2Ω=1+α, and Ω²−Ω+114=0. This uses the integral formula for Ω,
not division by 2 inside the endomorphism ring. With the usual
infinity parameter −x/y, dω=ζ, dF=0; hence dα=u, the fixed residue
embedding of sqrt(−455). Arithmetic Frobenius sends the tangent
sign to −u; the geometric endomorphism identity is
FαF⁻¹=−α−2F, NOT FαF⁻¹=−α. Normalize by the tangent, rather than
conflating concrete endomorphism conjugation with CM-field conjugation.

The elliptic dual satisfies dual(ω)=ω², dual(F)=−F,
dual(J)=−J and dual(V)=−V, hence dual(Ω)=1−Ω and
deg(Ω−z)=z²−z+114 for integer z, by multiplying by its dual.
At q=2,3,17,19 the residual roots of that polynomial are
(0,1), (0,1), (8,10), (0,1). For the indicated representatives
each norm has q-valuation exactly one. If Ω were any root scalar
on all A[q], then Ω−z would kill A[q], factor [q], and have degree
divisible by q², contradiction. Both residual eigenlines therefore
occur, and the distinct-root lifted idempotents split the Tate
lattice into rank-one summands. With w₀=(β+1)/2=30438, the exact
chosen / other eigenscalars modulo the full prime powers are

    m       16   3   289  361
    w₀       6   0    93  114
    1−w₀    11   1   197  248.

Thus the actual kernel of (Ω−w₀) on A[m] has order m and is
cyclic in each slot; product is the specified C_N of order N.
At 2 the Ω roots, not α modulo 2, distinguish the lines.
Moreover β²+455=185·4N and Ω acts on C_N by w₀ exactly.
Conjugating the CM embedding at the conjugate residue sign
switches w₀ to 1−w₀ and β to −β, so it is not the same input
unless the orientation is transported explicitly.

The integral embedding O_K→End(A,C_N) given by Ω is optimal
because the order is maximal and endomorphisms in this quadratic
subfield are integral. [Cornut–Jetchev, §4.10, Cor. 4.1](https://webusers.imj-prg.fr/~christophe.cornut/papers/liftings.pdf#page=15)
gives the actual enhanced CM lifting, not just a matching j-value.
[Elkies–Ono–Yang, §3.6](https://people.math.wisc.edu/~tonghaiyang/deuring.pdf)
specifies the normalized embedding by its tangent residue; at an
inert prime exactly one of the two conjugate embeddings is normalized.
These two statements join on the same geometric A, cyclic C_N and
same chosen residue embedding. The starting pair need not be the
principal class: it belongs to some class in the proper β/u
orientation and that is sufficient for an unweighted full trace.

## The exact relative class schedule

In the basis w=(1+sqrt(−455))/2 choose
a=(29,w−2), b=(5,w−3), c=(7,w−4). The signed reduced form convention
is I(a0,b0,c0)=(a0,(-b0+sqrt(D))/2). The arithmetic checker multiplies
two integer HNF ideal bases in (1,w) and computes the signed norm
form, then verifies orders 5,2,2 and agreement with the previously
computed 20 reduced forms. Relative classes a^i b^j c^k are:

| i | j,k=0,0 | 1,0 | 0,1 | 1,1 |
|---:|---|---|---|---|
| 0 | (1,1,114) | (5,5,24) | (7,7,18) | (12,11,12) |
| 1 | (4,−3,29) | (6,−5,20) | (8,−5,15) | (3,−1,38) |
| 2 | (9,−7,14) | (6,1,19) | (2,−1,57) | (10,−5,12) |
| 3 | (9,7,14) | (6,−1,19) | (2,1,57) | (10,5,12) |
| 4 | (4,3,29) | (6,5,20) | (8,5,15) | (3,1,38) |

In use, follow a four times on the j=k=0 row and then three
branched edges for each i: (0,0)→(1,0) via b, (0,0)→(0,1) via c,
and (0,1)→(1,1) via b. This uses 19 quotients, four degree 29
and fifteen degree 5/7. The exact q,w pair defines the kernel
A[q]∩ker(Ω−w). At q=5,7 equivalently use α=0; at q=29 use
α=3. The norms of Ω−2, Ω−3, Ω−4 are 116,120,126, each with
valuation one at q=29,5,7 respectively. Each q-subgroup is
therefore exactly order q, not the whole q-torsion. The q=5,7
ideals are ramified in K, but the arrows are separable in characteristic
53 and horizontal for the maximal order.

For an edge f:A→A/A[ideal], quotienting the Ω-stable subgroup
gives Ω' with fΩ=Ω'f. Since f is separable, dα' retains u; since
deg(f) is prime to N, the actual image f(C_N) is exactly the same
level-root subgroup on the new A[N]. In characteristic zero the
same ideal quotient acts by source lattice (mathfrak a) going to
(mathfrak a I^{-1}). Good prime-to-53 CM quotients reduce to
these same arrows; prime-to-53 subgroup specialization and quotient
formation commute. Thus one may use the table as RELATIVE action
labels from the actual seed; if one instead calls the source-ideal
labels absolute they have an unknown common shift and the inverse
convention. Either way the same full unweighted sum is permuted.
Do not deduplicate repeated geometric reduced objects. This
letter-by-letter rule does not construct the π values in the table.

## The exact level-48 orientation in the mixed quotient

Put d=323. For an oriented form [A,B,C] with N|A and
B≡β mod2N, the translated τ+a/d row has primitive coefficients
[dA, dB−2Aa, dC−Ba+(A/d)a²] for gcd(a,d)=1 and discriminant
D d². The new middle coefficient is dβ≡1 mod96.
On the finite side, first pass to A_B=A/C_d, carrying Ω.
For a mixed translate quotient line inside A_B[d], dα kills all
A_B[d] and Ω_d=dΩ+(1−d)/2=(1+dα)/2 preserves that line,
so it descends. On the same transported cyclic level 48, the
eigenvalue is d w₀+(1−d)/2≡1 mod48, matching the new middle
coefficient via (B'+1)/2. At both primes of d the mixed unit
line is not Ω-stable because the two transverse letters have
different Ω eigenvalues. Thus this local comparison preserves
the conductor-323 orientation without pretending the full O_K
action descends through the mixed line. Finally χ_{−323}(−β)=1
since −β is a square modulo both 17 and 19, so the sign read in
the prior translated-form list agrees with χ_{−323}(a) under the
chosen β.

The executable JSON specifies ideal kernels, form classes,
relative edges, and orientation arithmetic only. Actual quotient
curves and same-map evaluations are separate work.
