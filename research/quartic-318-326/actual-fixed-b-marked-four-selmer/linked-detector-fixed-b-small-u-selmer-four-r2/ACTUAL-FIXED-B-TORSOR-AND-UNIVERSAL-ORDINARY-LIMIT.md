# A tractable fixed-b genus-one model and its structurally neutral ordinary test

Use the same \(b=8912209\cdot1185793321\), \(t=1/2399\),
accepted repaired h, and nineteen exact middle-coordinate
W cells of the preceding fixed-b/norm packets. For any nonzero
integer \(u\) write
\[
 \lambda=\frac{16u^4+24u^2+1}{32u^2},\qquad
 C_u:\quad W^2-t=bY^2,\quad Z^2-W^2=\lambda .
\]
This is precisely the surplus-root norm producer with the
global b class fixed. Its target raw Kummer class \(\alpha=(b,1,b)\)
on \(E_u:y^2=x(x-bt)(x+b\lambda)\) is the image of the actual
affine map
\[
 x=bW^2,\quad y=b^2WYZ .
\]
The exact reverse square roots and common-W quartic are as in
22eae52a. The curve has no rational point at infinity with
these equations since b is nonsquare; a rational point would
automatically have nonzero W,Y,Z (respectively \(t>0\),
\(t\) is nonsquare, \(\lambda>0\)). A global \(\alpha\) point
is not torsion. No claim of global existence is made here.

## One concrete complete local model

At \(u=258049=11\cdot23459\),
\[
 \lambda=\frac{70946129015908599398441}{2130857164832},\quad
 t+\lambda=\frac{170199763509166860814024791}{5111926338431968}.
\]
The exact computation gives a nonzero square residue of
\(32(K+u^2W_p^2)\) at each of the original nineteen cells; here
\(K=u^2\lambda\) and 32 is a square at these split primes.
Thus one obtains an actual local Z for **every** W in each
specified ball by ordinary Hensel, using the original b-class
on the other factor. The small-place open phases are as before:
u odd and prime to 3,17, with sufficiently negative W depth,
and b is a square in all three. In particular the depths
\(v_2W=-600,v_3W=-8,v_{17}W=-1\) are attainable and give the
same original folded pole square/depth consequences at the
accepted h.

For a complete all-place membership test, at every odd prime
off \(2 b\,2399\) the possible additional bad support lies in
u, the numerator of \(\lambda\), or that of \(\lambda+t\).
If \(b\) is locally a square, simply take W sufficiently
large p-adically to make both quotients square. If b is an
unramified nonsquare at such a p, \(W^2-bY^2=t\) forces
integral W,Y and t is a unit. The remaining cases are:

* \(p\mid u\): \(\lambda\) dominates \(W^2\) at even negative
  depth and in unit class 2. Thus local compatibility is
  exactly \((2/p)=+\); the first norm equation has integral
  solutions by the norm in the unramified degree-two field.
* Positive \(v_p(\lambda)\): take a unit W on the first
  conic and then \(W^2+\lambda\) is a square unit. At odd
  \(p\ge5\) the nonzero finite norm fiber has \(p+1\) points;
  at most two have W=0, so choose and lift another.
* Positive \(v_p(\lambda+t)\): reduction forces \(W^2=t\)
  modulo p since the two nonzero residual squareclasses
  would otherwise conflict. Subtract the equations:
  \(Z^2-bY^2=\lambda+t\), whose valuation must be even.
  Conversely if t is square unit and this positive depth
  even, choose Z,Y from the unramified norm representation
  at that even depth, and Hensel \(W^2=t+b Y^2\) near its
  two unit roots. This is the exact local criterion there.
* At all other good odd places the smooth genus-one
  reduction has a finite-field point by Hasse and it lifts.

For the actual small u, the primes in its support are either
b-split or 2-split, and the complete support of
\(\lambda+t\)'s numerator is
\(3,51071,226691,4900372089410977\), all b-split.
The \(\lambda\) numerator factors \(97,36833,966041,20555323601\).
Every stated primality and product is replayed. The two
b-movers are exactly the retained balls, 2399 is b-split,
the small 2/3 phases are covered, and real W large works.
Thus this particular \(C_u\) is everywhere locally soluble
with all nineteen prescribed local balls, not just at a sample.

## A forced second Selmer direction for any such odd u

For this fixed b and t, let u be any odd integer prime to 3,
with \(\alpha\) locally soluble everywhere. There is always
another class \(\gamma=(1,2,2)\) in the full 2-Selmer group,
independent of \(\alpha\) and the rational torsion plane.

At an odd prime where 2 is square this is immediate.
At any odd p where 2 is nonsquare, p does not divide
b or 2399 (both b primes are 1 mod 8 and 2399 is 7 mod8).
The numerator of \(\lambda\) has no such prime divisor:
it is the primitive norm \((4u^2+3)^2-8\), and divisibility
would make 2 square. Away from u and \(\lambda+t\) the
curve is good and the whole unramified unit Kummer subgroup
occurs. At p dividing u, the all-place \(\alpha\) requires
b square if 2 is nonsquare, as above. Choose \(x\) a nonzero
square residue with \(x-bt\) a nonsquare unit. Then
\(x+b\lambda\) is in leading class 2 at even negative depth.
At p dividing \(\lambda+t\), choose the same x; now the
last two coordinates are both the same nonsquare residue
because the roots collide. For \(p\ge5\) the required
residue \(x=z^2\ne0\) exists: the character sum of
\(z^2-c\) for nonzero c is \(-1\); after excluding z=0
there remain at least \((p-3)/2\) z with nonsquare
nonzero value. Hensel gives actual local points with
these exact Kummer coordinates. At 3 one can take x=1
since \(bt=2,\lambda=1,b=1\bmod3\).
At 2 take x=9: \(bt\equiv7\bmod16\), and \(\lambda\) has
depth \(-5\) with unit phase 1 mod8, so both
\(x-bt\) and \(x+b\lambda\) have squareclass 2.
At infinity all entries of \(\gamma\) are squares.

Rational nonzero 2-torsion at x=0 or x=\(-b\lambda\)
has negative first signed Kummer coordinate, whereas
at x=bt it has first class \(b\cdot2399\), neither 1
nor b. Thus none of the three nonidentity positive tuples
\(\alpha,\gamma,\alpha\gamma\) is torsion, and \(\alpha,\gamma\)
are independent modulo the rational torsion plane. The same first-coordinate
test shows no nonzero 2-torsion is rationally doubled,
so there is no higher rational 2-power torsion.
In particular full \({\rm Sel}_2\) dimension at least 4
is structural; trying other u cannot produce the
dimension-three rank-one shortcut.

## Their ordinary pairing is universally zero on this family

Use the literal tangent formula for the ordinary
Cassels form. Only i=1,2 matter since \(\gamma_0=1\).
For the split conic \(W^2-Z^2+\lambda=0\) use its
rational tangent point \(((1-\lambda)/2,(1+\lambda)/2)\).
With \(D'=Z+W\ne0\), its evaluation is exactly
\[
 L_1=-\frac{\lambda(D'-1)^2}{2D'} .
\]
Here \(\lambda\) is a norm from \(\mathbb Q(\sqrt2)\)
by the above numerator identity, with \(32 u^2\) itself
a norm as well. Also \(-1/2\) is a norm. Thus the
local \((L_1,2)\) equals \((D',2)\).
For the other tangent use the same fixed exact conic point
\[
 (W_0,Y_0)=(4619710060,41)/(2399\cdot38613147)
\]
so \(W_0^2-bY_0^2=t\). In the \(E_u\) tangent normalization
the evaluation is \(L_2=b(W_0W-bY_0Y-t)\).

At all 2-split places both Hilbert factors are trivial.
At odd 2-inert p where b is nonsquare, W,Y and the seed
W0,Y0 are integral since t is a unit; \(\lambda\) is a
unit, by primitive norm and the exclusion \(p\mid u\)
from the local \(\alpha\) gate. Hence Z is integral and
\(D'(Z-W)=\lambda\) makes D' a unit. Replace (W,Y) by
its negative if necessary to make \(W_0W-bY_0Y-t\)
a nonzero residue (one of the two signs works). Then
both Hilbert signs are positive. Perturb in the same
smooth local curve if an exact tangent vanishes.

At an odd 2-inert p where b is split, and at the dyadic
place (using its actual Hilbert symbol),
take \(W\) of sufficiently negative depth and
\(Y\sim W/\sqrt b,\ Z\sim W\) with those signs.
Then \(D'\sim2W\) and \(L_2\sim b W g_p\), where
\(g_p=W_0-\sqrt b\,Y_0\). Here \(\sim\) means identical
squareclass when the depth is sufficiently large,
by the asymptotics and Hensel. Since 2 is a norm,
b is a local square, and W appears twice, the local
pairing product is exactly \((g_p,2)\). It is independent
of the sign of \(\sqrt b\) because the two g values have
product \(t=N(49+\sqrt2)^{-1}\).
At odd such p outside the fixed seed denominator both
g values are integral and have product t a unit,
so they are units and the sign is positive. The only
nontrivial odd contribution is p=3:
\(38613147=3\cdot12871049\), the second prime and
2399 are 2-split, while at 3 the two seed coordinates
have depth \(-1\); one g has depth \(-1\) and the other
\(+1\), so the Hilbert sign is negative.
At 2 the seed residues are \(W_0=4,Y_0=5\bmod8\),
\(\sqrt b=3\) or \(5\bmod8\); the g unit is 3 or 5
and its symbol with 2 is negative. The two negatives
therefore cancel globally. This argument does not
calculate or constrain pairings with any further Selmer
directions.

## Complete numerical 2-Selmer / Sel4 boundary at u=258049

The actual 30-bit squareclass matrix enumerates the
global constrained subspace exactly: at each odd
bad place four distinct local classes are explicitly
witnessed (the cardinal of \(E(\mathbf Q_p)/2\)), and
at 2 eight. Outside the exact bad support the unramified
unit image gives no more constraints. The two real sign
bits must agree in the first two coordinates, since the
third root is negative and the second positive.
The kernel dimension is 4, and the quotient by the
torsion plane has basis \(\alpha,\gamma\). The explicit
numeric tangent/Hensel replay also gives zero pairing
on this basis, independently of the preceding family
argument (different tangent normalization can shift
local signs by rational reciprocity). Thus \(\alpha\)
really is in the image of Sel4 on this exact
locally selected model. The full Selmer corank can
still be 0 or 2; an actual higher descent or a
rational affine point on the displayed quartic is
needed to decide. No rational static-W approximation
or full detector condition is inferred.

Replay from this directory (Python, SymPy, Python-FLINT):

    python3 check_fixed_b_local_258049.py | cmp - EXACT-LOCAL-258049.json
    python3 check_small_fixed_b_selmer.py 258049 | cmp - EXACT-SEL2-258049.json
    python3 find_small_fixed_b_pairing_rows.py 258049 | cmp - EXACT-CASSELS-258049.json
