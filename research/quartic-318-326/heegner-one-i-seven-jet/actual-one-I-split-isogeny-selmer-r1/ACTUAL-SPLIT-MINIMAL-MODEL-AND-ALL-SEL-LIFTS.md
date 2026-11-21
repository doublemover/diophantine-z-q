# One globally minimal actual split and lifts at every power of 2

Fix only the literal base \(d=2811626664334219040035976315\),
\(p=114649,\ q=119851,\ P=pq,\ \beta=Bb\), where
\(B=41579528353,\ b=4921145\). No companion twist, theta residue,
global point, or rank lower bound is claimed.

## 1. The two local survivors are a single geometric problem

The normalized negative and positive split systems are respectively

    q x² − p y² + B u² = 0,     q x² − 9p y² + b v² = 0;
    p x² − q y² − b u² = 0,     p x² − 9q y² − B v² = 0.

They are Q-isomorphic via \((x,y,u,v)\mapsto(3y,x,v,3u)\);
the same map in reverse composes to projective scalar 3.
In the earlier unnormalized quartic variable this is
\(A\mapsto3P/A\). If \(V^2=(A^2-P)(A^2-9P)/\beta\), the resulting
\(V'=3P\,V/A^2\); hence the two branches give the same original
marked point on \(E_d\) up to negation (the resulting U changes
sign; W and Z do not). There is no independent branch to reject
without rejecting the other. Work only with the negative pair.

Its actual degree-4 map to the split Jacobian
\[
 J:\quad Y^2=X(X-d)(X-9d)
\]
is
\[
 X=\beta q^2 x^2/y^2,\qquad
 Y=\beta^2 q^2 xuv/y^3.
\]
Indeed the exact full-2-descent triple (in the displayed root order)
is \((\beta,-b q,-B q)\). The three factors specialize as

    X      = β(q x/y)²,
    X−d    = (−bq)(B u/y)²,
    X−9d   = (−Bq)(b v/y)².

This identifies the degree-4 map with the standard full rational
2-torsion Kummer **2-cover**, not a multiplication-by-4 cover;
see [Fisher §5, equation (6)](https://www.dpmms.cam.ac.uk/~taf1000/papers/higherdesc.pdf).
The positive split differs from this Kummer triple by the class
of \((0,0)\) on \(J\), namely \((1,-d,-d)\).
The curve \(J\) is the exact 2-isogenous quotient of the original
\(E_d:y^2=x(x-d)(x+3d)\) by its point \((d,0)\): shift that
root to 0 to get \(y^2=z(z^2+5dz+4d^2)\), whose ordinary 2-isogeny
has coefficients \(-10d,9d^2\). For the original marked witness
use the already verified direct back-map
\(A=qx/y,\ V=quv/y^2\), not a generic 2-isogeny push.

## 2. Genuine global minimization of the negative model

Let \(Q_1,Q_2\) be its two original normalized integral quadrics.
Substitute \(u=x+y+2u'\), \(v=x+y+2v'\), keeping x and y.
Then \(Q_1\) is coefficientwise divisible by 2, and
\(Q_2−Q_1\) by 4 (both \(B,b\equiv1\bmod4\)).
Use the new pair \(Q_1/2,(Q_2−Q_1)/4\) after that substitution.
The product of the determinants of the variable and quadric
changes is exactly \(4/8=1/2\). This is a given rational
equivalence, with inverse explicit in the original coordinates,
not an existence claim about minimizing an arbitrary quartic.

With the Hessian convention of [Cremona–Fisher–Stoll,
Definition 2.4 and Theorem 2.8](https://www.dpmms.cam.ac.uk/~taf1000/papers/minred-234.pdf),
the original pencil determinant is
\(-16d\,\lambda\mu(\lambda+\mu)(\lambda+9\mu)\).
From it the original invariants are \(2^4c_4(J),2^6c_6(J),2^{12}\Delta(J)\).
The new exact invariants read
\[
 c_4=16\cdot73\,d^2,\quad c_6=64\cdot595\,d^3,\quad
 \Delta=2^{10}3^4d^6
\]
and equal those of the displayed integral Weierstrass model of \(J\).
This confirms the sign of the twist as well. At every prime the
displayed valuation of \(\Delta(J)\) is <12 using squarefree \(d\)
prime to 6. An integral rationally equivalent genus-one model
can only change the discriminant valuation by multiples of 12
(weight 12), so the new pair is globally minimal. This does not
assert archimedean reduction or rational solubility.

## 3. Exact full local Sel₂ on the same J

The exact Kummer calculation uses the pairs of the first two
root classes, the third determined by their product. The global
basis is −1 and the twelve primes dividing \(6d\).
At odd good primes the local Kummer group is precisely the
unramified subgroup: the elliptic scheme has good reduction,
[2] is étale, and the image has order 4, as does the unramified
subspace for the constant full J[2]. Thus all global squareclass
coordinates are supported on this displayed basis and there
are no further good-prime restrictions.

At each retained odd place, two independent exact local
Kummer witnesses span the full image. This follows from the
open pro-\(\ell\) formal group on which [2] is invertible,
and the finite quotient, giving \(|J(\mathbf Q_\ell)/2|=|J[2]|=4\).
At 2 there are three independent witnesses: an open formal
group is isomorphic additively to \(\mathbb Z_2\), where the
index is two and kernel zero, hence the full index is
\(2|J[2]|=8\). Over R the three real roots give two
components and index 2. All witnesses are archived in the
JSON. For a non-root x, each witness has exact square cubic
in its given completion; at a root the standard Kummer value
for that factor is the product of its two differences.
The checker uses valuation parity and the odd unit Legendre
class, or at 2 valuation parity and unit mod8, and exact
real signs. These local witnesses establish **both** inclusions:
they are actual points over the local field and there are
enough independent ones to span by the index calculation.
The annihilating rows have rank 23 on the 26 global bits.
Thus \(\dim_{\mathbb F_2}\operatorname{Sel}_2(J)=3\).
The archived target \((\beta,-bq,-Bq)\) lies in it and is
independent of the two rational 2-torsion Kummer classes.
No rational point with that non-torsion class is inferred.

## 4. Exact local-to-global 4/8 lifts; no rejection at any finite power

The Selmer exact sequence and full rational 2-torsion give
\(|\Sha(J)[2]|\le2\). In any abelian group with this property,
each \(\Sha(J)[2^m]\) is finite and cyclic: the doubling fibers
have at most two points so finiteness follows by induction,
and a finite abelian 2-group of 2-rank at most one is cyclic.
Thus every element of \(\Sha(J)[2^m]\) pairs trivially with
\(\Sha(J)[2]\) by alternation of Cassels–Tate on this cyclic
subgroup. Apply [Fisher, Theorem 3.1(ii), with the isogeny
[2]](https://www.dpmms.cam.ac.uk/~taf1000/papers/higherdesc.pdf):
its exact kernel/image criterion holds without assuming finite
Sha. This makes every such element the double of an element
of Sha, necessarily killed by \(2^{m+1}\). Therefore
\[
 [2]:\Sha(J)[2^{m+1}]\twoheadrightarrow\Sha(J)[2^m].
\]
The natural Kummer diagram projects rational points
\(J(\mathbb Q)/2^{m+1}\to J(\mathbb Q)/2^m\) by the ordinary
quotient map; on Sha it induces the doubling just proved.
Lift the Sha image and then adjust the lift by a rational
Kummer class to obtain the specified lower class. This
gives **surjectivity** of all Selmer transition maps induced
by \([2]:J[2^{m+1}]\to J[2^m]\).
In particular the literal cover class here has actual
everywhere locally soluble multiplication-by-4 and
multiplication-by-8 covering lifts, and compatible lifts
at every larger finite power of 2. This proves existence
of these lifts, not their explicit equations or a rational
point on one of them. Higher 2-descent cannot reject this
class by a local Selmer obstruction at any finite level.
An explicit high-degree lift may still help find a global
point; the possible divisible Sha branch is not excluded.

    python3 -B check_actual_minimal_intersection.py | cmp - EXACT-MINIMAL-INTERSECTION.json
    python3 -B check_isogenous_exact_selmer.py | cmp - EXACT-ISOGENOUS-SEL2.json
