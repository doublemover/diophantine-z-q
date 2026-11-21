# An actual rational point on two original factors, and its exact denominator failure

Keep the literal scalar \(J\), the four exact recurrence labels, all
sixteen old \(w\bmod p^2\) cells including historical \(p_a=415721\),
and the two positive-root cells of the repaired numeric cover with
\(q_1=8912209,\ q_2=1185793321\). Write
\[
 b=q_1q_2=10568037907556089,\quad
 s=-32/407,\quad t=1/2399,\quad W=c_1w.
\]
This records an actual numerical rational point on the **two marked
factor equations**, and genuine order and small-place preparation
for it. Unlike an abstract corank or Selmer-four observation, no
pointwise converse supplies this rational point. The *same* proposed
complete detector fails its actual reduced square denominator at
two explicitly known additional inert primes. It is therefore not
a rational PointPair or a quartic witness.

## Rational point first, one prime left

The exact small ternary seed
\[
 (X_0,Y_0,Z_0)=(4619710060,41,38613147),\qquad
 X_0^2-b Y_0^2=2399 Z_0^2
\]
parametrizes the repaired positive-factor conic by multiplying
\((X_0+Y_0\sqrt b)/(2399 Z_0)\) by
\((v+u\sqrt b)/(v-u\sqrt b)\). In particular
\[
 W=\frac{X_0(v^2+b u^2)+2bY_0 u v}{2399 Z_0(v^2-b u^2)},\qquad
 Y=\frac{Y_0(v^2+b u^2)+2X_0 u v}{2399 Z_0(v^2-b u^2)} .
\]
Hence \(W^2-bY^2=t\) identically on this actual parameterization.

Use primitive projective local ratio coordinates to impose all
eighteen selected \(W\) residues. At each place this is one homogeneous
linear congruence in \((u,v)\) modulo the certified precision:
choose \(v_0u-u_0v=0\bmod p^k\) and exclude a common \(p\)-factor.
At the fixed small places choose the strict negative depths of \(W\)
explicitly; in particular \(v_2 W=-600,\ v_3 W=-8,\ v_{17} W=-1\).
The \(W\)-chart inverse uses
\[
 \lambda=2399 (W W_0 - bY Y_0'),\quad
 \mu=2399(Y W_0-WY_0'),\quad u/v=\mu/(1+\lambda),
 \quad (W_0,Y_0')=(X_0,Y_0)/(2399 Z_0).
\]
The exact local projective conditions give one rank-two lattice
of determinant of bit length 1725. Gaussian reduction in the
real-tilted form \( (K u,v-\lfloor\sqrt b\rfloor u)\),
\(K=\lfloor\sqrt b\rfloor/100\) rounded down, puts the search near a
positive real pole of this conic parameterization. The selected
coordinates relative to its ordered reduced basis are \((259,-181)\).
The archived exact \(W=X/Z>2\) has a reduced 1762-bit numerator
and 1758-bit denominator. Its units and all eighteen local cells
are tested on the **exact fraction**, not inferred from a probable
prime test or a floating reconstruction.

The remaining negative factor is exactly
\[
 W^2-s=\frac{p_a q_a C^2}{Z^2}.
\]
The exact integers \(q_a,C,X,Z,Y\) are in the point JSON.
The one new \(q_a\) has 3505 bits (1055 decimal digits), whose
canonical decimal SHA-256 is
b5bf27f831d44eeaaf06f5356cce9d861e69964846d9d462d950e86155f12e26.
It was **proved prime** by Python-FLINT 0.8.0 / FLINT 3.3.1
(the version's [proved primality routine](https://raw.githubusercontent.com/flintlib/flint/v3.3.1/src/fmpz/is_prime.c),
not is_probable_prime; about 175 s on the author machine).
The optional bounded search uses probable screening only; the
separate replay completes the proof of this exact prime.
Set \(a=p_a q_a\) and \(D=ab\). Then
\((W,C/Z,Y)\) is an exact rational affine point on the original
normalized two-factor cover
\(W^2-s=aU_0^2,\ W^2-t=bV_0^2\).
The marked affine point on \(E_D:y^2=x(x-Ds)(x-Dt)\) is
\((D W^2,D^2W(C/Z)Y)\).
This is not a rank-only argument or an abstract rational localization.

## Actual index and selected-place denominator gates

At the new prime the exact residue \(\rho=\sqrt2\) and Gaussian
\(q_a=A^2+C_g^2\) yield candidate annihilators from
\(q_a+1\pm2A\). Use **actual** finite Jacobian order tests on
\(R\), not an assumption about its finite-group exponent. The
count gcd is a power of 2, and the old mover primes are prime
to both counts. Clipping a count \(G\) on a previous modulus \(L\)
and specified \(h_0\) means repeatedly dividing by
\(\gcd(G,L)/\gcd(\gcd(G,L),h_0)\) until it equals 1. It produces
the maximal divisor \(A'\mid G\) with \(\gcd(A',L)\mid h_0\):
this follows prime by prime by reducing an offending exponent
until it reaches \(v_p(h_0)\), and never changing a nonoffending
exponent. The opposite test uses \(h_0-1\) and the odd part.
Annihilation by the clipped count is directly verified, so no
factorization of the enormous group counts or minimal-order
assumption is needed.

The selected two literal annihilators have gcd 1 and the
original common \(h\)-congruence is maintained. In addition
\(h\equiv0\bmod A'_+\), \(h\equiv1\bmod A'_-\), and
\(h\equiv q_a^3\bmod q_a^4\). The least representative has 23705
bits on a 23706-bit modulus. The formal-parameter residues
at both lifted annihilators modulo \(q_a^2\) are nonzero
multiples of \(q_a\). The exact Luca residues at these huge
moduli use repeated gcd to strip the \(s_{\rm Lucas}-2\) factors;
no expansion of either actual large label occurs.
The lifted original reciprocal products provide the exact
three scales modulo \(q_a^2\): each is a unit, the twelve
nonzero roots in \(w^2\) are distinct and all three \(\Delta\)
are units. The new root is a single simple middle-scale contact
at \(s\), not a substitution of an unrelated middle scale.
The established literal formal-depth and XVI-leaf positive
theorem therefore gives \(v_{q_a} b_{241}=1\).
The three other selected movers (historical \(p_a\), and \(q_1,q_2\))
are exactly their inherited depth-one balls and source order
conditions, so they too give valuation \(+1\) in the middle pole.
At historical \(p_a\), for example,
\(T_{\rm mid}\equiv54777539872\bmod p_a^2\),
\(F(T_{\rm mid})/p_a\equiv285703\bmod p_a\),
and \(\Delta_{\rm mid}\equiv62306\bmod p_a\).
Nonsquare **values** there are allowed: the source at these places
needs a square reduced denominator, not even numerator valuation.

The h class retains \(h\equiv204\bmod289\), \(20\mid h\), and
the earlier dyadic/ternary progressions. The exact small-place
source-factor preparation gives the real pole valuation rows
at 2,3,17 from the established integral-leaf bounds:
\((1174,1318,1318),(18,6,18),(2,2,2)\), respectively.
Here the p=3 row increases by four from the earlier depth-six
local illustration because this **actual rational** \(W\) has
3-depth \(-8\). Each of these nine local pole values is a nonzero
square. At the real place \(W>2\) is exact, but does not by itself
verify the original real \(w^2\)-largeness/three-pole positivity
threshold after division by the actual \(c_1\).
For choosing h one may use the already proved even-progression
real density on this exact congruence, including a further finite
period if desired below. No numeric accepted real h, full
real \(w\) threshold, or numerical final original pole table is
asserted.

## Two exact fatal inert traces for the same W

The remaining factor \(W^2+1/2\) has two simple odd contacts at
\(p=94547,699211\), both \(3\bmod8\) and inert in \(\mathbf Q(\sqrt2)\).
The replay checks directly that \(F(W^2)\) has valuation one,
both \(c_1,\Delta\) are units, and the middle pole is therefore
in the original odd-contact chart. The actual restored data are:

| p | order of original R over Fp² | \(W^2\bmod p^2\) | \(F(W^2)\bmod p^2\) | \(N(U_h)\bmod p\) |
|---:|---:|---:|---:|---:|
| 94547 | 94548 | 6716855247 | 6126834694 | 7897 |
| 699211 | 699210 | 357154531561 | 200228159593 | 247527 |

For the retained least h (and its refinements modulo the
archived two \(p\cdot{\rm ord}(R)\) periods), compute the actual
inert coherent chart values over \(\mathbf F_{p^2}\).
All Padé and primary/alternate ratio denominators are units
and so all 16 unweighted leaf components are integral.
In particular the first coefficient is \(w_{126}=N(U_h)^2\),
a unit **rational** coefficient. The first weight has depth
\(-7\). At steps 2 and 3 the weights have depth \(-1\),
so the repeatedly squared first term strictly dominates.
From step 4 on the new weighted term is never below \(-25\);
the running term from the preceding square is already below
\(-25\). Hence there is no cancellation at any step and the
fold depth is exactly \(-7\cdot 2^{15}=-229376\).
Its leading coefficient remains rational and nonzero in
\(\mathbf F_p\). Writing the fold as \(X+Y\sqrt2\), this gives
\(v(X)=-229376 < v(Y)\); the actual inverse trace
\((X^2-2Y^2)/(2X)\) also has depth \(-229376\).
The exact pole identity yields at BOTH primes
\[
 v_p(b_{241})=1+2(-229376)=-458751 .
\]
Thus the rational reduced denominator has an odd exponent
458751 at each prime. This precise depth statement holds at
the same further h progression, and the independent original
inert early-eight theorem already rules out a valid nonzero
middle denominator at this W for **any** admitted h:
a split oriented solution cannot exist at these inert
ordinary odd contacts. The outcome is therefore not repaired
by changing the common real representative. The obstruction
is from the two *remaining* root factors, not the intended
positive valuation at historical p_a or another selected mover.

## Replay

From this directory, with Python 3 and pinned Python-FLINT 0.8.0,
GMPy2 2.2.1 for the large lifted arithmetic (the optional search
also uses SymPy), and the same source-only sibling donors:

    python3 prove_new_prime.py
    python3 check_affine_values_and_crt.py EXACT-RATIONAL-TWO-FACTOR-W.json | cmp - EXACT-ANNIHILATOR-CRT.json
    python3 check_new_p2_and_retain_cells.py EXACT-RATIONAL-TWO-FACTOR-W.json EXACT-ANNIHILATOR-CRT.json | cmp - EXACT-NEW-P2-AND-H.json
    python3 check_fatal_inert_traces.py EXACT-RATIONAL-TWO-FACTOR-W.json EXACT-NEW-P2-AND-H.json | cmp - EXACT-FATAL-INERT-TRACES.json

No use of an October rank converse, Cassels–Tate on this new
numerical curve, or any revised original polynomial.
