# A numerical positive-factor cover retaining all sixteen original contact cells

This is a finite rational witness for **one equation** from the same-scale
construction at the positive root of the unscaled slot. It is not a numerical
same-scale two-factor twist, a PointPair, or a proof of the joined result. In
fact it cannot be used for the full original saturation: the exact squareclass
below is nonsquare at the original anchor prime 23.

## Inputs and literal scale

Use the same scalar \(J\), \(i=6^{15}3^{65536}J\), recurrence labels
\(n=(3723,1+i,U_{k+1}(1+i),U_k(1+i)/(i-1))\), \(k=2(i-1)\), and inherited
\(h\)-residue class as the XVI packet. Here \(U_0=0,U_1=1,U_{j+1}=sU_j-U_{j-1}\).
The sixteen actual archived \(w\bmod p^2\) balls are unchanged. Set \(W=c_1w\)
with the *actual* same-index coefficient \(c_1=(A_++A_-)/2+A_+A_-\);
the matching residues are \(W_p=c_{1,p}w_p\bmod p^2\), not new choices of
old cells. At the two new primes, \(c_0=1,c_1,c_2=A_+A_-\) are
computed anew from the same reciprocal chart, with the same labels.

Take \(p=5268121,\ q=21191329,\ b=pq=111638485322809\), and
\(T_+=1/2399\). In order, the Gaussian generators are \(765+2164\mathrm i\)
and \(177+4600\mathrm i\) (here \(\mathrm i=\sqrt{-1}\), not the scalar index).
The following are literal finite-field point orders of \(R\) on the two
respective \(\sqrt 2\)-arms, *not* just the sizes of the groups:

| new prime | primary embedding of \(\sqrt 2\) | primary point order | opposite point order | signed Gaussian group counts |
|---:|---:|---:|---:|---:|
| 5268121 | 2108966 | 1317413 | 164581 | 5266592, 5269652 |
| 21191329 | 3018173 | 1324436 | 5297921 | 21190976, 21191684 |

Both have the exact historical positive-type phase at
\(3,5,7,11,37,2399\): \((+,+,-,+,-,+)\), and both are \(1\bmod 8\).
They are mutually square and the count product at each is prime to the
other and to all sixteen old contact primes. In each arm the first formal
return has valuation exactly one. Exact simultaneous congruences
\(h=0\bmod o_+\), \(h=1\bmod o_-\), \(h=p^3\bmod p^4\) (and the same at
\(q\)) extend the full archived \(h\)-congruence, not only its reduced
point-order part. The replay gives a positive 2648-bit \(h\) already at the
least CRT representative, with true original real norm in
\([-3170730933515255810,-3170730933515255809]/2^{64}\). The margin
\(|N(U_h)|>1/100\) does not concern the real magnitude of \(w\); the rational
conic below instead separately certifies \(W>2\).

At the new primes the archived residue \(W_p\) is a square root of \(T_++b\)
modulo \(p^2\), so the new shifted factor has exact valuation one. The program
checks every literal row among all three scales: the middle scaled row has
the unique simple positive-root contact; the other two full polynomial
values are units, the twelve nonzero roots are distinct, and the relevant
\(1-c_1^2w^2\) is a unit. In these two residue rows the *full unnormalized
monic five-factor polynomial* at the contact, divided by the prime,
has residue \(301965\) and \(14624835\), respectively. This establishes
the finite positive-factor local data, not an exhaustive prime-support
check for the other factors.

## Exact rational conic point

The integral seed
\((X,Y,Z)=(166124172,1,3384835)\) is checked by direct integers:
\(X^2-bY^2=2399Z^2\). Thus \(W_0=X/(2399Z),Y_0=1/(2399Z)\) gives the
needed nonzero norm. Multiply \(W_0+Y_0\sqrt b\) by
\((V+U\sqrt b)/(V-U\sqrt b)\) to obtain
\[
W=\frac{X(V^2+bU^2)+2bUV}{2399Z(V^2-bU^2)},\qquad
Y=\frac{V^2+bU^2+2XU V}{2399Z(V^2-bU^2)}.
\]
The exact \([U:V]\) and both reduced rational coordinates are recorded
in the output (no floating arithmetic). To build them, root-lift the
necessary unit \((W_p^2-T_+)/b\) at the XVI small balls, take \(Y\equiv\pm1\)
at either new prime, and invert this same rational norm-one chart.
The chosen projective congruence modulus at each of these eighteen primes
is two powers beyond the denominator valuation. The replay checks the
rational output itself in every ball and checks \(v_p(Y)=0\) at both new
primes. Separate exact congruences on \([U:V]\) yield \(v_p(W)\le-5\) at
\(2,3,5,7,11,17,37,2399\); the resulting eight depths are
\((-16,-19,-15,-17,-16,-16,-16,-16)\). Here all eight are legitimate unit
square places for \(b\). An exact sign comparison gives \(W>2\).

The rational identity \(W^2-bY^2=T_+\) implies **complete** positive-root
odd support on this equation: after reducing rational numbers, the parity
support of \(W^2-T_+\) consists of precisely \(p,q\). It says nothing similar
about \(W^2+32/407\), the other scale roots, or \(F\)'s total odd support.
It also does not give \(w>2\): only \(W=c_1w>2\) was asserted and checked.

## Why this is smaller than the original saturation

The full historical condition includes a square unit \(b\) at every prime
of the literal \(B\), including \(23\mid 76176!\mid B\).
This exact \(b\) is a nonsquare unit at 23, and \(W\) is integral there.
No choice of a deeper denominator at 23 can turn \(b\) into a square unit.
In particular a search reproducing both full Gaussian congruence classes
should not expect these primes: congruence to a fixed small Gaussian
generator \(\pi_0\) modulo the integer modulus \(M=8B L_0\) forces any
different generator norm to be at least
\((8\cdot 76176!-\max(|\Re\pi_0|,|\Im\pi_0|))^2\).
For \(\pi_0=3057+680\mathrm i\) this lower bound already has 677597 decimal
digits; it is a limitation of this sufficient literal ray, not a lower
bound on all valid production primes.

Reproduction from the parent directory of this packet:

    python3 linked-detector-numeric-old-compatible-positive-cover-r2/check_exact_numeric_positive_cover.py > /tmp/positive-factor.json

The script pins the earlier contact, formal-group, and interval implementations
by SHA-256; a replay computes all the displayed values from scratch.
