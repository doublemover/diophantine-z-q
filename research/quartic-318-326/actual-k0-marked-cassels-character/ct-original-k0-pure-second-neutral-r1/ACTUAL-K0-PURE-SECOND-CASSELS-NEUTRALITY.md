# The whole pure-second Kummer subspace is neutral against the k=0 mark

This holds for **every numerical Ready pole**, including a genuine detector or scalar pole, and not merely the ten known primes of one scalar. It is a statement about a paired Selmer class, not a rational-point proof or a universal other-direction obstruction.

Use the literal \(0<\mu=b/17=A/D^2<1\), \((A,D)=1\), \(C=D^2-A\), \(\beta=[A]\) represented positively and squarefree. The actual binary quartic in the unchanged \(k=0\) direction has marked Selmer class \(\Lambda=(1,C,C)\) on the integral Jacobian
\[
 y^2=x(x-4A^2)(x-A(A+3D^2)).
\]
This follows from the [literal Jacobian and torsor computation](../ct-original-k0-direct-isogeny-r1/LITERAL-K0-JACOBIAN-AND-DUAL-SEARCH.md). The rank or other directions are not assumed. If C is square, the mark is trivial and the assertion below is immediate. Otherwise, for **any actual** \(\eta=(1,d,d)\in\operatorname{Sel}_2(J)\), take signed squarefree d. Then
\[
                 \langle\Lambda,\eta\rangle_{\rm Cas}=+1.
\]
In fact at each place v, with the particular integral tangent normalization below, the product of the two contributing symbols is precisely
\[
                 (L_2(P_v)L_3(P_v),d)_v=(2\beta,d)_v.
\]
The normalized local statement uses these choices of rational tangent forms; the global sign is independent of their common normalization. Hilbert reciprocity immediately gives the assertion.

## 1. Local unit and valuation cuts on any genuine test class

Ready gives \(D\) prime to 6, \(v_2(A)=m\ge4\) even, \(\mu\) square at 2, \(v_3(A)=n\ge2\) even, and the class of A at 3 is the nonsquare unit 17 (since b is square). Thus \(\beta\) has class 1 at 2 and class 2 at 3. The first coordinate of \(\eta\) being 1 means that actual local representatives with generic x have x square. Local Kummer coordinates at the four exceptional torsion sites may also be deduced by continuity from ordinary points (elliptic curves over these local fields are smooth, and the Kummer map to a finite squareclass group is locally constant).

* **At 2**, divide x/y by \(2^m,2^{3m/2}\), so the second root has depth \(m+2\) and the third root is a unit of class 3. If the square x has valuation less than m, its second factor has the same class, since the two differ by a factor in \(1+16\mathbb Z_2\). If its valuation equals m, then the second factor differs from its class by \(1-4\cdot\mathrm{odd}\equiv5\bmod8\), and the third factor also has class 5. If its valuation is greater than m, the third factor again has class \(-3=5\). Hence **d has local class 1 or 5**, so in particular it is odd as a squarefree integer.
* **At 3** the two nonzero root depths are \(2n,n+1\), with \(n+1\) odd. A square x cannot be at depth \(n+1\). Below it all three factors have equal squareclass, hence all are square. Above it the third factor has class \([-3A]=[3]\) (since \(-A\) is square here, after removing its even valuation). Thus **d has local class 1 or 3**.
* **At odd p dividing \(\beta\)**, the torsion tuples at roots 0 and \(4A^2\) are
  \[
    ([3A],[-1],[-3A]),\qquad (1,[-3A],[-3A]).
  \]
  This uses that \(C\equiv D^2\bmod p\) is a unit square and \(A+3D^2\) has local class 3 there. The two valuation patterns \((1,0,1),(0,1,1)\) span the local four-element Kummer image. Consequently d has local class 1 or \([-3\beta]\), with the latter exactly when \(p\mid d\).
* **At all other finite p≥5**, the only possible odd valuations of d lie at \(p\mid C\). Indeed at a good prime the three roots are distinct and every Kummer valuation is even, including after a negative x-depth where the cubic valuation is three times the same depth. If \(p\mid A,\ p\nmid\beta\), divide x/y by \(p^{v_p(A)},p^{3v_p(A)/2}\); the first two roots collide and the third is a singleton modulo p. A singleton slot always has even valuation: if x is integral and close to that root, the other factors are units and the cubic square forces even valuation; at an integral x away it is a unit; a negative x-depth is even by the cubic equation. This applies to the third slot d. Likewise at \(p\mid A+3D^2\) the singleton is the second slot d. There are no hidden bad denominator places: at \(p\mid D,\ p\ge5\), the integral model has three distinct roots modulo p. At \(p\mid C,\ p\ge5\), \(\beta\) is local square because \(A\equiv D^2\bmod p\) and \(\mu=\beta c^2\).

This valuation classification is not a full Selmer-admission criterion and does not assert that every allowed d occurs.

## 2. Same integral tangents give the exact Hilbert product

Use the two quadrics and all three rational tangent points from the [actual integral contact formula](../ct-original-k0-contact-cassels-r1/ACTUAL-CONTACT-CASSELS-REJECTION.md), in projective coordinates \(z_1,z_2,z_3,t\). In Cassels' explicit formula the first tangent argument is paired with 1, and the others are
\[
   L_2=(3D^2-A)z_1-3DCz_3-A(A+3D^2)t,\qquad L_3=z_1-2At.
\]
The Cassels product formula used here is [Cassels, Second descents for elliptic curves, §7](https://doi.org/10.1515/crll.1998.039); its marked Cassels–Tate interpretation is [Fisher, The Yoga of the Cassels–Tate Pairing, Theorem 5.2](https://www.dpmms.cam.ac.uk/~taf1000/papers/casselspairing.pdf). The covered curve is everywhere local by the original \(k=0\) proof.

* **Odd p dividing A, p≥5.** Use \((z_1,z_2,z_3,t)=(s,1,-1,0)\) for the root \(s^2=C\) with \(s\equiv D\bmod p\). Then \(L_2L_3\equiv6D^4\bmod p\); the symbol equals \((6/p)^{v_p(d)}\). If the exponent is odd, p divides \(\beta\) by §1, and \(d=[-3\beta]\) locally. Here \((\beta,d)_p=(\beta,-3\beta)_p=(\beta,3)_p=(3/p)\) since \((a,a)_p=(a,-1)_p\). Hence \((2\beta,d)_p=(6/p)\). If the exponent is even, all symbols are trivial (at p dividing \(\beta\) this means d locally square).
* **Odd p dividing C, p≥5.** Use \(t=1,z_2=(1+3A)/2,z_3=(1-3A)/2\) and the root \(z_1^2=4A^2+Cz_2^2\) with \(z_1\equiv-2A\). The product is a unit congruent to \(32A^3\), hence unit class 2 since \(A\equiv D^2\). Also \(\beta\) is square there, so the symbol is \((2\beta,d)_p\).
* **Odd p dividing \(A+3D^2\), p≥5.** Take \(s\equiv2D\), as above with \(C\equiv4D^2\); the product consists of units. The parity lemma makes d a unit, hence both symbols are trivial. At every remaining good p both \(\beta,d\) are units, and the two supplied tangent products with their opposite sides give even valuation of each tangent at primitive points: \(L_3(z_1+2At)=Cz_2^2\), and \(L_2(r+A(A+3D^2)t)=C s_0^2\) where \(r=(3D^2-A)z_1-3DCz_3\), \(s_0=3Dz_1-(3D^2-A)z_3\). In the nonunit tangent branch the opposite side is a unit, as in the earlier integral calculation.
* **At 2 or 3**, choose \(s=D u\), where \(u^2=\delta\). Use the same infinity point \((s,1,-1,0)\); now \(L_2L_3=s^2(s+D)(s+2D)\) has the class of \((u+1)(u+2)\). At 2, take \(u\equiv1\bmod8\). If \(m=4\), then \(u\equiv9\bmod16\), \((u+1)/2\equiv5\bmod8\), and \(u+2\equiv3\bmod8\), giving class 14. If \(m\ge6\) these last two units are 1 and 3, giving class 6. For either class and \(d=1\) or 5 locally, the odd factors pair trivially with d, so the symbol equals \((2,d)_2=(2\beta,d)_2\). At 3 take \(u\equiv1\bmod9\), giving class 6. For d of class 1 or 3, \((6,d)_3=+1\), since \((6,3)_3=(2,3)_3(3,3)_3=(-1)(-1)\). This equals \((2\beta,d)_3\) because \(2\beta\) is a unit square at 3.
* **At infinity**, use \(s=+\sqrt C\). The product is positive, as is \(2\beta\), so the equality holds even for signed negative d.

These local equalities give the exact global sign by Hilbert reciprocity. No choice of actual Selmer-admission witness or new prime has been assumed in the local proof.

## 3. Consequence on the exact original a=0 scalar

On the [fixed original scalar at its own admissible index](../ct-actual-scalar-k0-supported-admission-r1/ACTUAL-SCALAR-SUPPORTED-K0-SELMER-CUT.md), the pure-second subspace can be discarded **even when it has arbitrary unknown prime support**. Moreover the first coordinate of a prospective nontrivial pairing witness cannot be supported using only \(\beta\) and primes of C: at every odd p dividing C the first Kummer slot always is square (the singleton root has square difference from the cluster). All C primes are ≥5 by Ready. Removing those primes leaves a positive squarefree divisor of \(\beta\) (x has no negative real class on this Jacobian), and the eight literal contact rows in that packet force it to be 1. Therefore any useful Cassels witness on this original scalar has genuinely new first-coordinate support. Possible sites to examine are 2 or 3, primitive even-depth numerator primes of A, or primes of \(A+3D^2\), not merely another factor of \(\theta\). This does not say such a witness exists, nor that it is necessary for every method of deciding k=0. No other-direction or four-pole source claim follows.
