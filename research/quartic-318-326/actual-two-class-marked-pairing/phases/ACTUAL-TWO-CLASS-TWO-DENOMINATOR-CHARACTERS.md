# Two exact denominator characters carry the first tested Cassels row

Continue with the exact two-factor cover and actual Selmer basis
of 7a597052 and 653cd000. Write a=sigma_a, b=sigma_b,
D=ab, s=s_a<0 and t=s_b>0. The desired mark is
alpha=(D,b,a). Its two Cassels tests on the verified
three-dimensional pair-supported subspace W are

    P_a = product_{p|a} (L_0(P_p)L_1(P_p), a)_p,
    P_b = product_{p|b} (L_0(P_p)L_1(P_p), b)_p,

with *primitive integral homogeneous* tangent representatives.
All other places were eliminated in the preceding proof.
We identify these tests with two exact rational denominator
characters. We do not compute either character or infer
that the desired torsor class vanishes.

At every p|a the units b,s,t,s−t are squares. At every p|b the
units a,t,t−s are squares. All four p are 1 mod8, so 2 and −1
are squares. These are exactly the cloned pilot phases in
the previous proof; all normalized roots are still the
literal old ones.

## 1. Choose local affine tangents with square values at the active primes

Use affine target conics, with normalization Z=1:

    H_0: a U_0²−b V_0²=t−s,
    H_1: W_1²−b V_1²=t.

The affine polar forms in variables (W,Z,U,V) are

    l_0=a U_0 U−b V_0 V−(t−s)Z,
    l_1=W_1 W−b V_1 V−t Z.

Each H_i has a rational conic point and hence weak approximation,
as previously proved by its local projections. We can prescribe
the following finite neighborhoods of affine points before choosing
rational Q_0,Q_1.

At p|a, choose on C a local point at U=0 with
W²=s and b V²=s−t; take Z=1. Choose Q_0 locally with U_0=1
and V_0²=(s−t+a)/b, and the sign V_0≡−V mod p. The unit
square condition on s−t and b and simple Hensel give this
choice. Its l_0 value is congruent to 2(s−t) mod p, a
nonzero square.

For l_1 at the same p, put r=√b in Q_p, a unit. The affine
conic H_1 can be described by X=W+rV, Y=W−rV with X Y=t.
Our chosen point on C projects to a point of this conic, with
X=X_* a unit. Choose X_Q a p-adic unit with the same square
residue character as X_* but a different residue. There are
many such units since p>76176. Put Y_Q=t/X_Q and use the
associated W_1,V_1 for Q_1. On the conic the polar value is

    l_1(P_p)= (t/2) (X_*−X_Q)²/(X_* X_Q),

a nonzero square residue since t/2 and X_*X_Q are squares.
Thus both affine tangent values can be held as square units
by fixed finite local neighborhoods at the two primes of a.

At p|b, choose on C a local point at V=0 with
W²=t and a U²=t−s, Z=1. Choose on H_0 the point
V_0=1 with U_0²=(t−s+b)/a, taking U_0≡−U mod p.
Choose on H_1 the point V_1=1 with W_1²=t+b, taking
W_1≡−W mod p. Then l_0(P_p)≡−2(t−s) and
l_1(P_p)≡−2t mod p, both nonzero squares. Again the
root choices exist by simple Hensel. We may perturb
these C-points locally to avoid any other tangent zero
without changing these two unit signs. The Cassels
formula allows arbitrary local points on C; these choices
need not reproduce the previously prescribed contact balls.

Weak approximation now gives global rational affine points
Q_0=(U_0,V_0) and Q_1=(W_1,V_1) integral at every
p|D, with all the above finite congruences. No unsupported
strong approximation or denominator restriction is imposed.

## 2. The primitive tangent scalars are the surviving variables

Let g_0>0 and g_1>0 be the least common denominators of
the affine coordinates of Q_0 and Q_1 respectively.
They are coprime to D. The vectors (g_0 U_0,g_0 V_0,g_0)
and (g_1 W_1,g_1 V_1,g_1) are primitive: any common
integer divisor would shorten the coordinate denominator.
Thus L_0=g_0 l_0 and L_1=g_1 l_1 are valid choices for
the compact four-place Cassels formula. The affine l_i
values are square units at all four tested primes. For
p|a (or p|b), the local Hilbert symbol of a p-unit g
against that squarefree parameter is the ordinary Legendre
symbol (g/p). Hence exactly

    P_a = (g_0 g_1 / a),       P_b = (g_0 g_1 / b),           (A)

with positive odd Jacobi denominators. The scalar
corrections in (A) cannot simply be dropped at these
four primes. A rational scalar has total Hilbert product
one over all places, but an affine unscaled tangent may
have introduced denominator contributions outside the
four-place cutoff.

At any odd r|g_0 outside B D, the equation of H_0 has
a,b,t−s units. At least one of U_0,V_0 has negative
valuation. Their depths must be the same and negative,
or the smaller doubled valuation could not cancel to give
the unit on the right. Dividing by that common square
power of r and reducing gives b/a a square unit mod r.
Thus D=ab is a square unit there. Likewise if an odd
r|g_1 lies outside B D, equal negative depths on H_1 show
b a square mod r. At r|B both a,b are local squares from
saturation, and r|D is not a divisor of either g_i.
Since D,b are positive and 1 mod8, Jacobi reciprocity
including the factor 2 therefore gives

    (g_0 / D)=+1,       (g_1 / b)=+1.

So the two actual test signs reduce to

    kappa = (g_0 / b) = (g_0 / a),     lambda=(g_1 / a),
    P_b=kappa,                        P_a=kappa lambda.      (B)

These equalities hold for any rational tangent choices
in the normalized neighborhoods just specified. They
do not assert either character is +. Note that they
are not first-order Legendre symbols of the support
primes alone; they involve rational affine conic solutions.

## 3. Exact arithmetic that remains

The two conics in (B) are genuine norm equations:

    N_{Q(sqrt(D))/Q}(a U_0+V_0 sqrt(D)) = a(t−s),
    N_{Q(sqrt(b))/Q}(2399 c_2 (W_1+V_1 sqrt(b))) = 2399.

The second equality uses t=1/(2399 c_2²); normalization
multipliers have support contained in B (or in a for
the first norm), so one must preserve the original
affine denominators when applying (B). An oriented
norm-ideal or higher reciprocity calculation would have
to certify these two characters. Ordinary weak
approximation of the tangent points does not determine
them. No actual numerical q_a,q_b or tangent points
are available from the prime-existence proof; this
is an exact reduction, not an evaluated second descent.

If kappa or lambda is −, one of the two pairing tests
obstructs a rational point on the desired two-class
curve. If both are + it proves orthogonality only to W,
not the rest of Sel_2 or a rational point; even full
orthogonality is a Sel_4 lifting statement. This does
not decide [C] in Sha(E_D)[2] and gives no new Lean or
PointPair conclusion.
