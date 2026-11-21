# One prescribed complete contact class reduces to a conic

Fix the same three actual rational scales c_j and literal five roots
of F. Let B be the exact positive collision-saturation integer of the
three-scale router (f0016ec0), in particular containing 76176!, all
scale numerators and denominators, all nonzero root numerators and
denominators and root-minus-one numerators, and the primitive
nonzero cross determinants. The twelve nonzero scaled roots are
distinct for these literal scales.

Use one common square t=w² with w in Q. For this result require the
following *depth*, not equality of the denominator to B^N:

    v_l(w) <= −2 v_l(B) for every prime l dividing B.

Arbitrarily stronger finite lower bounds on reciprocal sizes at
these same places, and an arbitrarily large positive real w, are
allowed. For l|B, v_l(c_j²w²) <= −2v_l(B) < v_l(theta_i) for every
nonzero theta_i. Thus all factor depths are negative even, and each
factor is a square in Q_l: write it as (c_j w)²(1−theta_i/(c_j w)²);
the second factor is a principal square unit, also at 2 since B
includes the factorial. For p outside B, if v_p(w)<0 all factors
have the same negative even depth; if v_p(w)>0 only the zero root
can meet p and its depth is even. If w is a unit, only one nonzero
scaled root can meet p, by the fixed cross determinants. Hence the
same odd-support router and disjointness survive even if the reduced
denominator has *additional* prime divisors outside B. This result
does not prove that there is a choice with denominator exactly B^N.

## Exact finite assumptions for one class

Let a=(j,i), theta=theta_i≠0, be one fixed target class. Let S be the
finite set of previously specified good contact primes, with their
exact prescribed residues w_p modulo p²; each p is outside B, hits
one specified nonzero class to order exactly one, and all its other
nonzero class values are units. Keep these literal residues whether
or not p hits a.

Nominate a positive squarefree integer sigma coprime to B. The following
three conditions are necessary and sufficient for a rational w with
the stated local saturation and retained contacts, such that

    c_j² w²−theta = sigma·Y²,    Y in Q×,

and every prime dividing sigma is a simple contact of this class:

1. **Saturation.** sigma is a square in Q_l for every l|B.
   Equivalently it is a square unit at each such odd l and
   sigma≡1 mod8 at 2. For efficient verification a single residue
   square root modulo 8 times the odd part of B certifies this
   (by odd-unit lifting, the modular assertion is also equivalent).
2. **Fixed p² rows.** For p in S, write A_p=c_j² w_p²−theta mod p²
   using the literal scale. Put e=1 if p hits a, e=0 otherwise.
   Then p|sigma iff e=1, and the unit quotient
   (A_p/p^e)/(sigma/p^e) has square residue modulo p.
   For e=1 the mod-p² residue is needed, to define the stripped
   unit mod p. This is the exact diagonal or cross-symbol test
   of d1e83d8e. It preserves the full old residue w_p mod p²,
   not just the square character of the old factor.
3. **Unseen support.** At each q|sigma outside S, theta is a
   square modulo q. It is a unit there since q is outside B.

Necessity follows from the equality and exact simple contact:
at l|B the factor is a local square; at p in S the asserted quotient
is a unit square; at q|sigma the contact reduces X²=theta mod q,
where X=c_j w. No positive-valuation contact can come from a
denominator pole of w outside B.

## Local existence and weak approximation

Consider the smooth projective conic with affine chart

    X²−sigma Y²=theta,     X=c_j w.

At l|B take any w of sufficiently negative valuation, satisfying
the chosen stronger depth if needed. The first paragraph shows
X²−theta is a square, and sigma is a local square, giving a nonzero
Y. This produces an open affine neighborhood at that place.

At p in S take any representative of the exact ball w_p+p² Z_p.
The valuations of A_p and sigma are the same, and their quotient
is a unit with the prescribed square residue. Odd Hensel gives Y
nonzero. The whole w-ball is allowed; the weak-approximation
condition will be the inverse image of that exact ball on the
conic.

At q|sigma outside S use a square root of theta mod q and Hensel
on X²=theta+sigma, taking Y=1. The derivative is a unit and
v_q(X²−theta)=1; an open neighborhood on the conic keeps Y a q-unit
and preserves this exact valuation.

At any remaining finite p both theta and sigma are units and p is
odd. The finite-field norm from F_p[s]/(s²−sigma) to F_p is
surjective on units, either from the quadratic finite field or
from the product F_p×F_p. Thus X²−sigma Y²=theta has a residue
solution with at least one nonzero coordinate. Its gradient is
not zero, so the affine solution lifts by Hensel. No conditions
need to be prescribed at these unramified places.

Over R take w positive arbitrarily large, so every c_k² w² is
larger than all the roots. Since sigma>0, a nonzero real Y exists.

The [Hasse–Minkowski theorem, Sutherland Thm. 11.12](https://math.mit.edu/classes/18.782/2023sp/LectureNotes11.pdf)
now gives a rational point on the projective conic. Projection
from that point identifies the smooth conic with P¹ over Q.
Ordinary weak approximation on P¹ (weak approximation on Q in
finite affine charts, Thm. 11.7 of the same notes) realizes all
the finitely many open neighborhoods just specified, including
the real one. For clarity the finitely many omitted affine
points of P¹ cause no restriction: the open neighborhoods in a
local field always contain points off any finite set. We take the
result in the indicated affine chart. Then w is rational, Y≠0,
all old p² values are retained, and every q|sigma is simple.
The target factor therefore has full odd support exactly sigma.
At other classes this controls only the prescribed contacts
and common routing, not their full or even local marked support.

## Further reduction: a single extra prime, without the order constraint

Let K be the product of the primes in S already hitting a (possibly
K=1). Ignoring h/elliptic orders, there is always a completion of
the three conditions with sigma=Kq and one further prime q outside
B and S. Indeed impose

    q ≡ K⁻¹ modulo 8 times the odd part of B.

At every p in S, condition 2 for sigma=Kq fixes an individual
Legendre bit for q at p, after stripping p from both sides when
p|K; K/p or K is a fixed unit as appropriate. Choose a nonzero
residue in the prescribed square or nonsquare class at each p.
The modulus conditions are independent, and their common class
is reduced. Dirichlet provides infinitely many such primes q.
The displayed congruence supplies condition 1.

For condition 3, every prime dividing the numerator or denominator
of theta belongs to B. Since q≡K⁻¹≡K mod8, the factors −1 and 2
give the same symbols at q and at Jacobi denominator K. For each
odd l|B, quadratic reciprocity and q≡K mod4 give
(l/q)=(l/K), using (q/l)=(K/l) from the congruence. Hence
(theta/q)=(theta/K)=+1, because every previously assigned prime
p|K had theta square at its unit contact. This also covers K=1.
The construction is symbolic: the modulus can be enormous.

## Exact remaining arithmetic boundary

If, in addition, all primes of this nominated sigma admit the
actual common h compatible with the preceding CRT, original real
and small-place guards, and the strong primary/opposite orders
with the local depths for the original sixteen-leaf fold, then
that same h with the w produced above gives the pointwise
positive odd folded-pole valuations at the entire support of
this one class. Those elliptic group/depth and real-index
conditions are separate; Dirichlet does not certify them.
The conic removes any *additional* rationality obstruction for
this one class once the finite conditions hold. We do not have
an order-compatible extra prime from the displayed progression.

The theorem supplies no simultaneous rational solution to the
other eleven class equations (their intersection is not a
conic), does not assert all detector denominators are squares,
and does not give a rational PointPair or Lean result.
