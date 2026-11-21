# Exact fixed quotient of the actual two-class 2-Selmer group

**Scope.** Use the exact two-factor construction (manifest e649acb1) and its
anchored Rédei refinement (415469f3), with the same literal c₁,c₂,
s = −32/(407c₁²) < 0 < t = 1/(2399c₂²), and the distinct primes
pₐ=415721, qₐ, pᵦ=9807649, qᵦ. Write a=pₐqₐ, b=pᵦqᵦ, D=ab.
All four primes are 1 mod 8, the clones satisfy qᵢ≡pᵢ mod 8B for the
original saturation integer B, and the supports are disjoint from B.
This note gives the whole quotient as an exact fixed local linear system,
and computes a four-dimensional **relaxation of its known-support slice**.
It does not compute the full dimension, establish a full Selmer lift, or
supply a rational point. “Fixed” means independent of the two new primes,
not that the support of the literal coefficients has been factored.

## 1. Exact moving-prime elimination

Kummer coordinates are in root order 0,Ds,Dt on E_D:y²=x(x−Ds)(x−Dt);
write parity triples additively, with even coordinate sum. At any odd
p the local quotient E(Q_p)/2 has size four: an open formal subgroup has
invertible [2], and kernel and cokernel of [2] on the finite quotient
have the same size. The local kernel on the elliptic curve is the full
rational 2-torsion. At a moving prime all three root distances have
valuation one. The torsion rows and identity have four distinct
valuation triples, so exhaust the local quotient.

All six inter-prime Legendre symbols are +. For either within-pair
symbol, the inherited old pilot contact is literally
cᵢ²w²≡θᵢ+pᵢ mod pᵢ². Its prescribed square quotient by pᵢqᵢ forces
(qᵢ/pᵢ)=+; this is the unscaled factor at the prescribed w, not the
stored pole. For the four cross pairs, b is square at both primes of
a and a is square at both primes of b, since the fixed difference s−t
is a square unit at both pilots and thus at their clones, and the retained
opposite factor is square. Reciprocity forces the four bits equal,
and the exact pilot symbol (pₐ/pᵦ)=+ is checked in the replay.
At either prime of a, the signs of (s,t,s−t) are +++; all four torsion
unit-sign triples are therefore +++. At either prime of b the signs
of (s,t,s−t) are −++; the exact torsion row with valuation (v₀,vₛ,vₜ)
has unit signs ((−1)^vₜ,(−1)^vₜ,+). For example the rows at 0 and Ds
have unit signs --+, and the row at Dt has +++. Here D/p is square
and −1 is square. These are local images of the same twisted Jacobian.

Write a global triple as x pₐ^A qₐ^A′ pᵦ^C qᵦ^C′ coordinatewise,
where x is supported on B and sign, and all exponent triples are even.
Away from B and the moving primes the specified equation has good
odd reduction and all local valuations are even. At each prime of B,
the clone and pilot have the same local squareclass (including the
dyadic precision) and D is square; the square scaling to the base
E₁:y²=x(x−s)(x−t) preserves these Kummer coordinates. The same holds
over R. At the moving primes, reciprocity transports the B-supported
x signs from each pilot to its clone.

Let M be the fixed set of classes d = x pₐ^Ā pᵦ^C̄, with Ā any even
triple and C̄ in {000,110}. Require x all-square at pₐ, the third
coordinate xₜ square at pᵦ, and d in the exact local Kummer image of E₁
at each prime of B and infinity. Good unit places elsewhere do not add
conditions (the moving primes were treated separately). Then there is
an exact sequence of F₂-spaces
\[
 0\longrightarrow W\longrightarrow\operatorname{Sel}_2(E_D)
 \longrightarrow M\longrightarrow0 .
\]
The last map sends (A,A′,C,C′) to (A+A′,C+C′), retaining x.
The kernel is exactly the already computed three-dimensional W, the
same arbitrary even A=A′ at both primes of a, and C=C′ in {000,110}
at both primes of b. To lift any element of M, take A′=0 and A=Ā.
Let (−1)^e=(x₀/pᵦ)=(xₛ/pᵦ). Take C′=(e,0,e), C=C̄+C′.
The exact moving-prime rules check both pairs, and the fixed places
see exactly d.

Consequently dim Sel₂=3+dim M. Both rational torsion directions map
injectively to the actual torsion Kummer classes of E₁: in their rows
the moving valuation triples coincide in each pair and collapse to
zero; removing the factors D changes the remaining classes only by
squares under collapse. If the full M had dimension two, the already
tuned pairings against W would therefore give a full Selmer-four image
for α, **not** a rational point. That premise is not shown here.

## 2. Literal constants and exact odd two-root collision table

For the actual shallow charts put
\[
 \eta=c_1/c_2
 = 1+\operatorname{Re}\!\left(\prod_{j=0}^3 U([n_j]R)\right)
 =m/n,\qquad (m,n)=1,\quad n>0 .
\]
The given chart has ξ=∏(−1/U), c₁=Re ξ+Norm ξ and c₂=Norm ξ, so this
follows from Re(1/ξ). The n_j are the same four positive retuned labels:
3723, 1+i, ℰ_{2(i−1)+1}(1+i), ℰ_{2(i−1)}(1+i)/(i−1), where
i=6^15·3^65536·J on the pinned common-q scalar, and
ℰ₀=0, ℰ₁=1, ℰ_{r+2}(u)=uℰ_{r+1}(u)−ℰ_r(u).
Scaling x by (2399·407 c₁n)² gives the integral base roots 0,S,T:
\[
 S=-32\cdot407\cdot2399^2 n^2,\quad
 T=2399\cdot407^2 m^2,\quad
 T-S=2399\cdot407 P,\quad
 P=407m^2+32\cdot2399 n^2 .
\]
Thus the literal squareclasses of s,t,t−s are −814, 2399, and
[2399·407 P], respectively. No alternate ratio is used.

At odd p let just roots i,j collide, let k be separate,
let l=v_p(e_i−e_j)>0, and write ε=χ_p(e_i−e_k).
The exact local image has these rules:

* ε=+: the k-coordinate is square and the i,j coordinates are equal,
  ranging over all four local squareclasses.
* ε=−, l even: all and only unit triples occur.
* ε=−, l odd: valuations are 000 or the pair ij; in the first case the
  sign at k is + and in the second −. One of the adjacent signs is free
  and the other follows by the square product.

Indeed, away from the node integral affine x gives equal classes
in the two adjacent unit factors, so the separate coordinate (including
at separate torsion, using its derivative) is square. Nonintegral x gives
three copies of the class of x, hence trivial by the equation. At the node
the separate class has sign ε. If ε=− and either adjacent depth is <l,
the adjacent classes agree, which is impossible by the square product.
Otherwise both depths are ≥l and their minimum is l; product parity
forces both parities to equal l mod 2. The node-torsion rows obey the
same statements by the derivative convention. Each row rule allows
only four triples, so the exact size four already established proves
equality. At odd good primes a single nonunit factor must have even
valuation, and the same size gives all unit triples.

Outside {2,11,37,2399}, m,n,P are pairwise coprime. Substitution gives:

| Divisor | Colliding roots | Depth | ε | Nonzero valuation bit possible? |
| --- | --- | --- | --- | --- |
| p divides m | 0,T | 2v_p(m) | (814/p) | iff split |
| p divides n | 0,S | 2v_p(n) | (−2399/p) | iff split |
| p divides P | S,T | v_p(P) | (−814/p) | iff split or odd depth |
| none | no pair | 0 | n/a | no |

At p dividing P the norm identity gives (−814·2399/p)=+, hence
(−814/p)=(2399/p), not necessarily +. This table removes every
nonsplit even-depth column without factoring; each eligible column
has at most one static valuation bit. Let L be the set of eligible primes
(including the known 3,5). Then dim M≤12+|L|: at most three collapsed
bits, one sign bit (the middle coordinate is positive), two at each
of four exceptional primes, and one per eligible prime. This does not
determine the size of L.

## 3. Exact local rows at fixed small places

The exact residues of η mod p² at (3,5,11,17,37,2399) are respectively
(6,10,48,209,1269,1073341). The replay lifts the four U-charts in both
split arms or the inert quadratic ring, using the verified reduction
order and p times that order modulo p², the exact Lucas recurrence, and
exact denominator stripping in the fourth label. At p=3,5 the table
says precisely the middle coordinate is square. At p=17 all differences
are units. At p=11,37 the roots have valuations (1,2), and at 2399 they
have (2,1), because η is a unit at these three primes. The three actual
torsion rows and identity have distinct valuation triples and exhaust
the images. Their unit signs are in the replay.

At 2 the original doubling formula gives x([2]R)=U(R)^−2 with
v₂(U(R))=3/2: for R=(1+√2,2√2), the numerator x²+(3−√2)² has
valuation 1 and the denominator 2y valuation 5/2. We normalize
v₂(2)=1. Thus −x/y at [2]R lies in the formal disc with depth 3/2
and every [n_j] is odd, so preserves this depth. The identity
U([n_j]R)²=1/x([2n_j]R) gives depth 3/2 for every chart. Their
product has depth 6; its real coefficient has depth at least 6,
since in the basis 1,√2 the nonzero terms have distinct valuation
fractional parts. Hence η≡1 mod 64.

Use the square-scaled roots S₀=−32·407·2399² and T₀=2399·407²η²
(equal to S/n²,T/n²). S₀/32≡1 mod8 and T₀,T₀−S₀≡7 mod8.
The torsion rows give (2,2,1) and (−1,−1,1). The test x=S₀+640
gives classes (10,10,1): both first factors have odd valuation
and stripped unit 5 mod8, and x−T₀≡1 mod8. Their product is square,
so this is a Q₂ point. The three independent rows exhaust the image:
a sufficiently small open formal subgroup has index two under [2]
by the formal log, and the kernel/cokernel sequence for the finite
quotient makes |E(Q₂)/2|=2|E(Q₂)[2]|=8. Thus exactly the third coordinate
is square. Over R the interval between the negative root and 0
and the unbounded real component give precisely a positive middle
coordinate.

## 4. The finite known-support relaxation and its remaining tests

Restrict x to {-1,2,3,5,11,37,2399}. Impose the complete local tests
at these places and the moving-prime conditions, omitting other fixed
bad places. The replay exhausts all 2¹⁷ exponent choices and gives
**16** rows, with basis:

| x | Ā | C̄ |
| --- | --- | --- |
| (1,1,1) | 101 | 000 |
| (131945,1,131945) | 000 | 000 |
| (−1952786,814,−2399) | 000 | 000 |
| (2399,2399,1) | 011 | 110 |

Here 131945=5·11·2399. Only the third listed basis direction is
automatically in M; it is the actual torsion direction at the root 0.
The base torsion class at t might require unlisted primes. This result
is neither a lower nor an upper bound of four for the **whole** M.
Intersecting this finite four-dimensional space with the remaining
unit conditions gives exactly the actual known-support slice.

More precisely, for any such candidate d, its only remaining checks
at unlisted fixed primes are χ_p(dₛ)=+ at split p dividing m,
χ_p(dₜ)=+ at split p dividing n, and χ_p(d₀)=+ at split or
odd-depth p dividing P. One factor-free way to state the split checks
is that the respective rational unit is a square in the respective
quadratic ring modulo the clean modulus: Z[√814] modulo |m_clean|,
Z[√(−2399)] modulo n_clean, and Z[√(−814)] modulo P_clean. Cleaning
means deleting all tested and exceptional primes. Indeed a rational
unit is always square in an inert quadratic residue field, and at
odd prime powers the unit derivative lifts the roots. For the remaining
odd-depth P primes use (d₀,P_clean)_p=+ (a global norm formulation
also requires its other places). This is a criterion, not a computed
phase. In particular the first surviving row needs (pₐ/p)=+ at
every extra split p dividing n; splitting in Q√(−2399) alone cannot
force this independent quadratic character. These square tests for
known-support rows also cannot detect potentially **nonzero** static
valuations at unknown eligible primes.

**Exact continuation.** Certified support/valuations for the literal
reduced m,n,P above, or a separate proof with equivalent rank
completeness, would complete the fixed linear algebra. Only the
odd valuation columns in the table are permitted. Factoring only the
odd-valuation squarefree parts of m,n,P is insufficient, since even-depth
split primes still supply potential columns. Neither the compact
elliptic circuit nor the verified finite residues certify full support.
No full factorization, complete rank, or additional higher pairing
evaluation is asserted.
