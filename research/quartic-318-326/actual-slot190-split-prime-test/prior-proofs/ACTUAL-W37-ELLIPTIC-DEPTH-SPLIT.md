# Complete signed elliptic depth split for the actual fixed slot190 norm

This is a paper reduction of the unknown fourth-power support remaining after
the fixed-index contact proof 8a0f698e. It is not a larger prime scan or a
claim that the remaining support is empty. Work with the same retained h
and w37, with original quadratic field K=Q(sqrt(2)), and put
d_c=3-sqrt(2), R=(1+sqrt(2),2 sqrt(2)). The literal auxiliary curve is

    E: y^2=x^3-d_c^2 x,      U(P)=2 y(P)/(x(P)^2+d_c^2),
    w37=N_(K/Q)(U([h]R)).

The donor 5a70adc6 retains h. All identities below are on this E and original
R, not on a replacement detector curve. The independent 313 row
b7c885a5 has distinct reduction orders 6 and 17; the torsion-free odd
unramified reduction kernel proved below shows R is not torsion. This also
makes all nonzero indexed points used below nonzero and nontorsion.

## 1. Exact signed local formula, including an opposite pole

Take an odd rational p other than 7. Then E has good reduction at every
prime w of K above p: its given discriminant is 64 d_c^6, with
N(d_c)=7. Its local field is unramified, with valuation normalized by
v_w(p)=1. Let a_w be the exact finite order of R mod w, and put

    mu_w = v_w(z([a_w]R)),    z=-x/y.

Here z is the parameter at infinity, and mu_w is a finite integer >=1.
For any m divisible by a_w, the exact formal formula is

    v_w(z([m]R))=mu_w + v_p(m) - v_p(a_w).                 (A)

Indeed, the integral invariant differential of this Weierstrass formal
group has constant coefficient 1 in z, so its formal logarithm has the
shape z + sum_(j>=2) c_(j-1) z^j/j with all c_i integral. If v_w(z)>=1
then j v_w(z)-v_p(j)>v_w(z) for j>=2 and odd p. Thus the logarithm
converges, is isometric on the formal disk, and its formal multiplication
identity gives (A). In particular that kernel is torsion-free without
choosing a rational holomorphic logarithm or entering bad reduction.

For P=[h]R and Q=[2h]R the duplication law gives

    U(P)^2=1/x(Q),    x([2]Q)=(x(Q)^2+d_c^2)^2/(4 y(Q)^2).

The only possible contribution to v_w(U(P)) is the following trichotomy:

| reduction of Q | exact contribution at w |
| --- | --- |
| O, i.e. a_w divides 2h | +(mu_w+v_p(h)-v_p(a_w)) |
| T0=(0,0) | -(mu_w+v_p(h)-v_p(a_w)) |
| all other reductions | 0 |

For the first row x on the formal disk has valuation -2 v_w(z), which
proves it by (A) with m=2h. In the second row x(Q) has positive
valuation. The numerator in x([2]Q) is then a unit and y(Q)^2 has
valuation v_w(x(Q)), so v_w(x([2]Q))=-v_w(x(Q)); use (A)
with m=4h. In this second row a_w divides 4h but does not divide
2h. Divisibility by 4h but not 2h is alone insufficient: the two
other order-two reductions of Q have unit x and contribute zero.
Outside O and T0 the x coordinate is a unit, including at those two
order-two points. All computations are on the same actual point and
multiplication-by-h, including when p is inert.

Norm valuation is exactly

    v_p(w37) = sum_(w | p) [k_w:F_p] v_w(U(P)).           (B)

So at split p add the two signed depths, and at inert p double
the single signed depth. In particular one cannot add both split
denominator depths and ignore a potentially opposite pole on the
other arm.

## 2. What a missing contact prime would actually certify

At split p the curve has four rational two-torsion points
O, (0,0), (d_c,0), (-d_c,0) over F_p. Its group cardinal is not divisible by p:
otherwise 4p would divide the cardinal, impossible by
#E(F_p) <= (sqrt(p)+1)^2 < 4p. In particular v_p(a_w)=0
on both split arms.

Assume a positive odd contact valuation e away from the fixed exceptions
of 8a0f698e (so c and Delta units, p not 2,3,7,17). Write s=v_p(h).
If the retained pole is nonzero and admits a literal PointPair, the exact
inequalities from (A),(B) and 8a0f698e are:

| types of the two split arms (up to order) | required inequality |
| --- | --- |
| +,+ | mu_1+mu_2+2s >= 3e+1 |
| +,0 | mu_+ + s >= 3e+1 |
| +,- | mu_+ - mu_- >= 3e+1 |
| no + arm | impossible |

At inert p the sole arm must be of type +, and
mu_w+s-v_p(a_w) >= ceil((3e+1)/2). These conditions are *exactly*
the contact theorem's necessary norm-depth condition, not sufficient for
PointPair. Away from p|h all nonzero arms have p-unital order a_w,
since a_w|4h. Then for e=1, a split +,+ prime needs either one arm
of depth >=3 or both arms of depth >=2; a split +,0 needs depth
>=4; a split +,- needs positive-arm depth >=5. Inert needs depth
>=2. For larger odd e the displayed inequalities retain the precise
extra depth.

Thus every viable new odd contact prime not dividing h is an actual
elliptic Wieferich prime in at least one **specified** arm for the original
R: z([a_w]R) vanishes modulo w^2, and hence so does z([#E(k_w)]R).
For a split prime with one pole arm and one positive arm, deepening h
by p-powers does not improve the net depth as long as its two types
stay fixed: the +s and -s exactly cancel.

## 3. Divisibility route and the precise remaining obstacle

For positive arm w let A_m be the denominator ideal of x([m]R) to
half exponent at the good places. This is defined exactly by local
valuation; at a place outside its denominator the exponent is zero.
By (A), w divides A_m iff a_w divides m, and if it does,

    v_w(A_m)=mu_w+v_p(m)-v_p(a_w).

In particular for p not dividing h, an eligible positive arm must have
first index a_w a divisor of 2h and v_w(A_(a_w))>=2, with the sharper
conditions above. A negative arm instead has first index dividing 4h
but not 2h; counting it as type - still requires Q mod w equal to T0.
This separates the finite h-support case from the actual, potentially
unseen squareful first-appearance factors of the original elliptic
denominator sequence. Neither order divisibility alone nor the
norm/product formula bounds those factors; a certified rank-of-apparition
power statement or equivalent restricted factor certificate would be a
genuine next input, not an assumption of this reduction.

The ordinary h-support part can in principle be certified by a
factorization of h and local orders/depths at its primes. For the
other part this argument specifies exactly the recurrence and the
power condition a future certificate must test. It neither excludes all
such primes nor asserts one has the correct contact signs. No global
witness, generic rank, or local Lean result is claimed.
