# Independent cold review: the fixed one-I split Jacobian

This review binds ACTUAL-SPLIT-MINIMAL-MODEL-AND-ALL-SEL-LIFTS.md
(SHA-256 8859410b295def62b2a2ae4150b3fcdec76b2b129b3ad22c4a4593a748046b14)
and author manifest
99c9f126d90eceb4284dd5d93fe1cf428824fb8a72a88af253d46a6f83740bdd.
The author outputs for full local Selmer and integral minimization
(48a2bc7e223cf7eaf5ba584508a8c459cd2394a8c55d060f687a1a081bcef5f3,
cfe0e3163f5605dc9ab55ba706b7b85e99d16d841051fe19b1cbf64dc60e2733)
both reproduced byte-for-byte. The separate Python script here uses explicit
finite square-residue sets, an independently assembled local annihilator, and
binary elimination; it does not import either author's checker.

**Verified for the same literal base.** Put \(d=2811626664334219040035976315\),
\(p=114649,\ q=119851,\ \beta=Bb\), as in the paper. The map of the
negative split to \(J:Y^2=X(X-d)(X-9d)\) gives the three root classes
\((\beta,-bq,-Bq)\), in that order. Its other surviving split
is isomorphic via \((x,y,u,v)\mapsto(3y,x,v,3u)\);
the alternate Kummer class differs by the class of \((0,0)\) of
\(J\). That second split supplies no independent obstruction.
The integral change \(u=x+y+2u',v=x+y+2v'\) and
\((Q_1/2,(Q_2-Q_1)/4)\) has total determinant \(1/2\).
The resulting \(c_4,c_6,\Delta\) are \(1168d^2,38080d^3,2^{10}3^4d^6\).
The discriminant weight is 12 and each displayed prime exponent is
less than 12, giving global minimality among integral equivalent
models. See [Cremona–Fisher–Stoll, Definitions 2.4, 3.3 and Theorem 2.8](https://arxiv.org/pdf/0908.1741).

**Full local test.** The independent check gives binary rank 23 on
the 26 possible global bits, hence dimension 3. At every other odd place
the distinct unit-separated roots and the fact that the cubic is a square
force all three valuations even; the unramified subgroup has precisely
the required order 4 and accounts for the whole local Kummer image.
At the retained odd primes the independent witnesses span order 4;
at 2 they span order 8, and at the real place order 2. These sizes follow
from the formal subgroup and compact finite quotient at the finite
places and from the two real components at infinity. Direct point counts
8 and 52 at the good primes 7 and 53 bound rational torsion by order 4;
the actual rational two-torsion realizes that order. The first coordinate
\(\beta\) is therefore outside the torsion Kummer span.

**Every finite lift, without a finiteness hypothesis.** From the
Selmer exact sequence, \(|\Sha(J)[2]|\le2\); by induction and the
structure theorem each finite-level \(\Sha(J)[2^m]\) is cyclic.
The alternating pairing pairs any element of this cyclic group
trivially with \(\Sha(J)[2]\). Apply [Fisher, Theorem 3.1(ii)](https://arxiv.org/pdf/1509.03234)
to the self-dual isogeny \([2]\): the exact annihilator criterion
does not assume finite \(\Sha\). A double preimage of an element killed
by \(2^m\) is killed by \(2^{m+1}\), so the adjacent
maps on the 2-primary torsion are onto. In the Kummer exact
diagram the left map is the ordinary rational quotient reduction
and the right map is this doubling. Lifting the right image and then
correcting with the left image proves surjectivity of the adjacent
Selmer maps induced by \([2]:J[2^{m+1}]\to J[2^m]\).
The literal marked degree-4 map is a multiplication-by-\(2\)
cover; its locally soluble multiplication-by-\(4\), multiplication-by-\(8\)
and higher lifts therefore exist.

**Limit.** There is no produced global rational point, rank lower
bound, given higher covering equation, or companion value. A nonzero
divisible 2-primary Tate–Shafarevich class has not been ruled out.
Neither this independent review nor these replays are a Lean check.

Reviewed independently, Vesper, 2026-11-21 UTC.
