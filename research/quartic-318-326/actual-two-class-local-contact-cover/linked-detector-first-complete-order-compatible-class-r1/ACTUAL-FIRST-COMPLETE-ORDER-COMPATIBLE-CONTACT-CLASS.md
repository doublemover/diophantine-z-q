# Paper existence of a complete order-compatible support in the literal slot 241 root −32/407

**Scope.** Keep the original literal J, all four labels and scales,
and the complete sixteen-contact congruences. The target is one
of the twelve nonzero root factors, not the entire detector product.
For the target c_1² w²+32/407 (slot 241), the statement proved
below gives positive squareclass 415721·q with precisely those
two odd-support primes, both simple and both having positive
valuation +1 in the unchanged stored pole at an actual common h.
All sixteen previously named valuations are retained. This is
existence, not a numeric q or a computed rational w. It does not
solve the other eleven support classes, yield square pole
denominators, a PointPair, or Lean.

Here B is the exact saturation-router integer of f0016ec0
for the fixed scales, S is the explicitly known set of sixteen
contact primes, and h* modulo L is their common even index CRT.
The exact existing residues w_p mod p² for p in S are retained.
The full denominator condition is the local depth at every l|B
in the one-class conic theorem (5a4bfc38), not d=B^N exactly.
All fixed original modulo-5 and scalar local conditions already
inside L are retained, not the old exact scalar output.

## 1. Exact pilot and reciprocal targets

Set K=Q(rho), rho²=2, G=Q(i), and E_d:y²=x³−d²x,
d=3−rho, R=(1+rho,2rho). Its conjugate uses d'=3+rho and R'.
The target pilot p₀=415721=475²+436² from the XVI data has
primary root rho=10923 mod p₀. Its literal counts and orders are

    primary      #E=414772,   ord R=103693;
    opposite     #E=416672,   ord R'=29.

The direct point-sum checker verifies the two counts; their gcd
is exactly 4. The actual order and residue rows are the independently
checked XVI output. Thus the full pilot order constraints already
hold in h* modulo L. All p in S are >76176, congruent to 1 mod8,
outside B, and have distinct exact scaled-root slots mod p.
Only p₀ hits the target class, with c_1² w_(p₀)²+32/407 congruent
to p₀ mod p₀².

If sigma=p₀ q, the stripped fixed p² unit condition in the conic
theorem prescribes a single bit eta_p=(q/p) independently at
each p in S. Explicitly, let A_p=c_1²w_p²+32/407 mod p² and
e_p=1 for p=p₀, 0 otherwise. The bit is the Legendre symbol of
(A_p/p^e_p)/(p₀/p^e_p); the quotient is a unit modulo p.
The checker computes all sixteen exact bits and exhibits unit
residue coordinates for them below. At p₀ the bit is +.

## 2. A finite field encoding all anchor order constraints

Write L_0 for L with the full prime powers of all p in S removed.
Set M_0=8 B L_0. This integer is coprime to every member of S.
Over G take the ray class field modulo the ideal (M_0), and
require the ray class of the Gaussian prime generator
pi₀=475+436i. An ideal in this ray class has a generator pi
congruent to pi₀ mod (M_0); the class number of G is one.

We impose finitely many additional Frobenius conditions on
the **actual points**, not a conjecture about full point orders.
Include K G. For each rational prime l|L_0, for each of the
two arms j=+,-, let g_j=v_l(#E_j(F_(p₀))) from the pilot.
Over KG adjoin the l^(g_j+1)-torsion of the two corresponding
curves. The arithmetic Frobenius determinant det(1−Frob) on
this module fixes the exact valuation of the group order to
g_j. Only work at good primes different from l.

For the primary arm put k=v_l(h*), for the opposite put
k=v_l(h*−1). If k>=v_l(L), there is no cap and no extra
division field needed. Otherwise also adjoin the splitting
field of the finite division fiber

    [l^g_j] D = [l^k] R_j.

This fiber has a local rational point mod a good degree-one
prime exactly when the l-primary component of [l^k]R_j there
is zero, PROVIDED v_l(group order)=g_j. Indeed [l^g_j]
annihilates the whole l-primary part of that finite group
and is invertible on its prime-to-l part. In particular the
criterion works even for noncyclic l-primary groups; it is
not an assumption that their exponent equals their order.
Existence of a rational point in this finite fiber is
equivalently a fixed geometric point of arithmetic
Frobenius. Good reduction identifies the geometric division
fiber and its Frobenius permutation with the residue fiber:
multiplication by l^g_j is finite étale on the smooth
elliptic scheme where l is invertible.

Take a Galois compositum F_0 over G of these fields, the
ray field, and their conjugates. They are unramified at
every prime above S. Indeed the displayed literal E_d
and E_d' have good reduction off 2,7; the points extend
over a good local model, and the torsion and division
fibers are finite étale off the same places and l.
KG/G is unramified off 2. Taking conjugates and a
compositum does not introduce another rational prime
of ramification. All possible rational primes of
ramification of F_0/G divide M_0.

Choose a place over (pi₀) with rho reducing to the marked
10923, and choose the actual Frobenius g₀ of F_0/G at
this place. It exists because p₀ does not divide M_0.
If a degree-one prime of G has this Frobenius conjugacy
class, choose the representative place with Frobenius g₀.
Its two marked arms therefore have, for every l|L_0, the
pilot group-order valuation and the required capped point
orders. In particular the opposite point order remains
odd: l=2 is in L_0, h* is even, so the opposite k=0,
and the pilot is odd. The restriction to KG is trivial,
so both marked rho arms are actual F_q-arms.

## 3. Independent finite ray conditions at the old contacts

For p in S the Gaussian residue ring is F_p×F_p.
Choose split coordinates (u_p,v_p) with neither in
mu_4(F_p), and with (u_p v_p/p)=eta_p. This always exists
here: 2 is a square not in mu_4 and either 2 or a
quadratic nonresidue supplies v_p. A nonsquare is outside
mu_4 at p=1 mod8. The literal choices and conversion
to real/imaginary coordinates are recorded in the checker.
For every joint unit multiple of the Gaussian generator,
these residues retain the norm sign and make both
N(pi−1),N(pi+1) prime to p. (Multiplication by any of
the four units preserves the exclusion from mu_4.)

CRT gives a class in the ray field F_S/G of modulus
product_{p in S}(p). F_S/G and F_0/G are linearly
disjoint: their intersection is abelian, unramified
at primes over S by F_0, and unramified elsewhere by
F_S. Here the ramification statement is RELATIVE TO G.
In particular F_S/G is unramified above 2, even though
G/Q itself ramifies at 2. There is no real place of G.
The Hilbert class field of G is G (Gaussian integers
are Euclidean). This proves the asserted trivial
intersection, including the dyadic issue. Both fields
are Galois, so the joint Frobenius class in F=F_0F_S
is nonempty and has a positive fixed density delta.

For the resulting degree-one primes let q=N(pi)=A²+C²,
with generator pi=A+Ci chosen congruent to pi₀ modulo
M_0. Thus A is odd, C is even, q≡p₀ mod M_0, and
(q/p)=eta_p for all p in S. Also q≡1 mod8 and
(7/q)=(q/7)=(p₀/7)=−1. By reciprocity (theta/q)=
(theta/p₀)=+ for theta=−32/407, since its rational
numerator and denominator support and 8 divide M_0.
We discard the finitely many primes dividing the fixed
data or lying in S.

## 4. Exact group orders and the one infinite coprimality sieve

At such q the two arm curves are quadratic twists:
d'/d=(d')²/7 is a nonsquare and scaling by a square root
gives the twist isomorphism. Thus their Frobenius traces
are opposite. Both counts are divisible by 4 because
each has full rational 2-torsion. Their unordered counts are

    G_±=q+1±2A=N(pi±1).

Here is a direct CM trace justification sufficient for
this formula. Since I:(x,y)↦(−x,i y) is over F_q and
I²=[−1], for any auxiliary l≡3 mod4, l≠q, Frobenius
on the 2D rational l-adic Tate module commutes with I
and hence belongs to the two-dimensional centralizer
Q_l[I]. If t is its integral trace and q its determinant,
then q−(t/2)² is a square in Q_l for all such l. The trace
is even from #E=0 mod4 and q=1 mod4; Hasse makes the
integer q−(t/2)² strictly positive. If it were not an
integer square, its nontrivial real quadratic character
and the character of −1 would be independent, so
Dirichlet would supply an odd l≡3 mod4 where it is a
nonsquare, a contradiction. Thus q=(t/2)²+C'² in Z.
Its odd coordinate t/2 is odd because t≡2 mod4, and
Gaussian unique factorization makes it ±A. The
quadratic twist interchanges the two traces (also
immediate from their character sums).

For l|M_0, cloning pi₀ precludes any odd common divisor
of G_+,G_− there, since the actual pilot gcd is 4.
For p in S the separate ray residues make both groups
prime-to-p, so anchor constraints at those primes hold.
At all other odd l, simultaneous divisibility requires

    A≡0 mod l,   C²≡−1 mod l.

It only occurs at l≡1 mod4. Forgetting the generator
unit, the bad residues comprise at most the single unit
orbit {±u, ±iu}, u²=−1 mod l, in the ray class group
of (l) over G. Its size is (l−1)²/4 by the unit quotient.
We may exclude this whole bad ray class, which is
slightly stronger than excluding only the normalized
generator condition.

For any fixed Y, impose these good ray classes at
l<=Y not dividing M_0 product_{p in S}p. The individual
ray extensions are linearly disjoint from F and each
preceding one: their intersection is abelian and
unramified at every relative finite place (the only
possible ramification of the new ray is above the new l),
and the Gaussian Hilbert class field is trivial. Hence
Chebotarev gives an asymptotic for this finite system
with density at least

    delta · product_{l≡1 mod4, l>=5} (1−4/(l−1)²) = delta · c > 0.

In particular this positive lower constant does not
shrink to zero as the fixed cutoff Y increases.

For the intermediate tail Y<l<=X^(1/4), use the
[Deshouillers–Gun–Ramaré–Sivaraman ray Brun–Titchmarsh theorem, Thm. 3](https://arxiv.org/pdf/2210.11051).
For the fixed field G and modulus (l) it gives the
single-class upper bound 2X/(h((l)) log(X/(u(G)l²))).
Here the norm of the ideal (l) is l², and for all
l<=X^(1/4) the logarithm is >=(log X)/4 for sufficiently
large X, with the same fixed u(G). Thus the count
in the union of all these bad classes is at most

    32 X/log X · sum_{l>Y} 1/(l−1)².

This upper bound does not require uniformity in the
large finite base field F. The constant delta · c is
fixed before choosing Y, and we make the tail <delta·c/4.

For l>X^(1/4), use the actual integer coordinates, not
an unproven equidistribution estimate. Since 0<|A|<=sqrt X
(the norm is a rational prime >2), l<=sqrt X and there
are O(sqrt X/l) possible nonzero A divisible by l.
The two possible residue classes of C have
O(sqrt X/l+1) entries in the box. Summing the product over
even all integers l with X^(1/4)<l<=sqrt X gives
O(X^(3/4)+sqrt X log X)=o(X/log X). Each degree-one
Gaussian prime ideal is represented by these Gaussian
coordinates up to the four units, which only changes
constants; degree>1 norm prime ideals are O(sqrt X)
and can be discarded. With Y fixed and X→∞, the positive
main term survives both tails. In particular infinitely
many different rational primes q realize the base
Frobenius and have odd group-order gcd 1.

## 5. Return to the actual common h and the one complete factor

Choose one such q, not dividing L. In the marked orientation
let a be the primary full order and b the opposite full
order. The caps cloned at every l|L_0 and prime-to-S
counts at the other divisors of L give
gcd(a,L)|h* and gcd(b,L)|(h*−1). Since b is odd and the
two counts share no odd factor, gcd(a,b)=1.
Neither count is divisible by q: by Hasse it is positive
and <2q at these large primes, and its multiple q would
be odd, contradicting full rational 2-torsion. Therefore
one generalized CRT simultaneously gives

    h=h* mod L,   h=0 mod a,   h=1 mod b,   h=q³ mod q^4.

This has an even progression. At q the primary formal-entry
depth is at least four (the first return has depth at least
one, multiplied by q³), and the opposite entry at h−1
has depth at least one. The independently checked
real-progression density theorem (629a0483) supplies
a positive h>1 in this exact progression with the actual
strict absolute norm margin. No numerical h is claimed.

For sigma=p₀q the old B square conditions hold because
q≡p₀ mod M_0 and p₀ is a unit at B. All exact old p²
rows have the requisite square-unit phases by the S ray.
The new prime q satisfies rho²=2 and theta square.
Apply the one-class conic theorem with its local depth
saturation and positive real w. It gives an actual rational
w, all retained p² rows, and full positive target
squareclass sigma, i.e.

    c_1² w²+32/407=(415721·q)·Y²,    Y in Q×,

with depth exactly one at both p₀ and q. At q the scaled
collision router puts all other roots in unit classes,
and Delta and c_1 are units. Thus the established
pointwise sixteen-leaf/trace fold yields +1 at q in slot
241; at p₀ and the fifteen other old contacts the cited
exact residues and the old index CRT retain their +1
values. This is a complete class with verified common
order compatibility at every prime of its support.
There is no compatible-support assertion for the other
eleven classes beyond the named old contacts.

Classical inputs are the usual prime-to-residue Tate module
and finite étale good reduction facts for elliptic curves,
Gaussian ray class theory and Chebotarev, the displayed
primary ray Brun–Titchmarsh bound, Hasse–Minkowski/weak
approximation, and the separately proved real-density lemma.
No GRH, unbounded trial-factor oracle, conjectural order
distribution, or actual numeric prime is used.

Finite donor replay (not a numerical replay of q):
    python3 -B check_complete_class_finite_donors.py | cmp - EXACT-FINITE-PILOT-AND-CROSS-RAY.json
    sha256sum -c SHA256SUMS
