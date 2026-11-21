# One constant-conductor marked receiver, and a uniform literal source gate at 29

Fix a *given* original Ready pole b with B=17b and μ₀=b/17=βc₀².
Write δ₀=1−μ₀, and let θ=[δ₀]. Here β,θ are positive nonsquare
squarefree classes, gcd(β,θ)=1, θ is square at 2 and 3 and at
every prime dividing β, and β is square at primes dividing θ.
The original materialized a=0 scalar has these guards and 5|β.
Use the literal c₀ and δ₀; no factorization of the large δ₀ is
needed in the geometric criterion. There is no rational point
on the actual receiver exhibited here.

## 1. Exact single quartic and rational back-map

Let G(t)=1−βt², H(t)=1−9βt², J(t)=1−81βt², and
D(t)=βG(t)H(t). Use the two first-mark parameter values t and 3t,
so D(3t)=βH(t)J(t). This gives one fixed genus-one receiver

    C: V²=δ₀ G(t)J(t).                                   (1)

There are four distinct branch points. For a rational point on
the projective curve (1), t is finite and nonzero: the boundary
values at 0 or infinity would require δ₀ square. Neither factor
in (1) can vanish rationally because β is nonsquare. Over the
reals (1) then forces 0<βt²<1/81 or βt²>1. In both ranges
D(t),D(3t)>0 and H(t), H(3t) are nonzero. The factors
1−3βt² and 1−27βt² also never vanish. Thus both actual ordinates
from the full mark formula are nonzero; the two parameters are
distinct; and neither first or second twist is zero.

Put h₀=V/(δ₀ G(t)), so the *exact* equality is
D(3t)=δ₀ D(t) h₀². The known full-mark point at a parameter u
is (X_u,Y_u) with

    A_u=1+3βu²,  X_u=β A_u²,
    Y_u=β A_u · (4βu) · 2(1−3βu²).

Use the first point on E_{D(t)}. Divide the second coordinates
by h₀²,h₀³ to put it on E_{δ₀ D(t)}, without changing the mark.
Now take λ₀=17c₀/A_t, λ₁=17c₀ h₀/A_{3t}, and put

    T=D(t)λ₀²,     s=B λ₀/λ₁,
    y₁=Y_t λ₀³,   y₂=(Y_{3t}/h₀³)(Bλ₀)³.

Since B=β(17c₀)², the resulting scaled abscissae are B and Bs²,
and the second curve parameter is TB²δ₀. Therefore

    y₁²=B(B−T)(B+3T),
    y₂²=(Bs²)(Bs²−TB²δ₀)(Bs²+3TB²δ₀),     s≠0,

literally NormalizedPolePoints318.PointPair. This is the original
same-b consumer; no substitute pole, fixed helper support, or
point at a common pole is used. The two output nontorsion claims
are not needed by this consumer; we have proved nonzero ordinates.

## 2. A constant-model marked point, not two simultaneous rank problems

Let d_raw=βδ₀. Taking X=δ₀/t², Y=δ₀ V/t³ in (1) gives
exactly the scalar x-class δ₀ on

    E′_d: Y²=X(X−d)(X−81d), d=d_raw.

This is reversible: take t²=δ₀/X from the specified x-class and
recover V. The only 2-torsion scalar x-classes are 1 and d, so
no excluded boundary is introduced. The positive squarefree
representative d=βθ gives the isomorphic model with the very
same κ class θ. Also the rational torsion class d interchanges
the θ and β tests, without identifying either with the trivial
class. In fact neither mark comes from any torsion: in real
root order 0<d<81d the sole T that could have a rational
half is at 81d, and that would require the nonsquare 81d
to be square by the usual root-difference criterion. Odd
torsion disappears in the exponent-two x-Kummer quotient.

The exact 2-isogenous model is

    E_d: Y²=X(X+16d)(X+25d).

The usual signed 2-isogeny with T₀=(0,0) changes coefficients
(a,b)=(41d,400d²) to (−2a,a²−4b)=(−82d,81d²),
so its scalar connecting map really is the stated x-class
on E′_d. Its base d=1 is
Y²+XY=X³+10X²+25X by x=4X, y=8Y+4X. This integral model has
discriminant 3⁴5⁴ and c₄=481, hence conductor 15, good at 2,
nonsplit multiplicative at 3 and split multiplicative at 5
(the slopes are detected by −16 mod 3 and 16 mod 5).

For the prepared congruence d≡17 (mod 24), 2 is unchanged,
3 becomes split, and the real sign is −. At good odd primes
ramifying in d, the local sign is (−1/p), whose product away
from 5 is + because d≡1 (mod 4). At 5 the local sign is
−(d/5) if 5∤d, and (−1/5)=+ if 5|d. These are the local
quadratic-twist formulas (e.g. [Bisatt, Theorem 1.7](https://research-information.bris.ac.uk/files/198735914/explicit_root_numbers.pdf)).
Consequently the literal a=0 class has sign +, not a parity
shortcut to rank. A prepared class prime to 5 with both β
and θ squares there has sign −, but still needs a proved
rank and a *marked* Kummer test. No original helper choices
alter this fixed d.

## 3. Exact local distinction: viable for original PointPair, not the strict old dyadic twist

A useful equivalent model over Q is the smooth two-conic
intersection

    βz²+δ₀ e²=1,       L²=16+9δ₀ e².                     (2)

For (1), set z=−10t/(1+9βt²),
L=5(9βt²−1)/(1+9βt²), e=V/[δ₀(1+9βt²)].
Conversely t=−z/(5−L), V=10δ₀e/(5−L). These are reversible
on the above literal rational locus. In particular the smaller
a priori sufficient test e=1 is precisely L²=25−9βc₀² with
z=±c₀. It will be ruled out for the entire fixed cyclic source
below. Equation (2) itself permits arbitrary rational e.

If δ₀ is square over a completion, start at z=0, e=1/√δ₀,
L=5. If β is square, start at z=1/√β,e=0,L=4. These are
smooth projective points and can be perturbed off the finite
excluded locus. This covers infinity, 2,3, and the supports
of β and θ. In applying these arguments one may first
replace δ₀ by θ, exactly rescaling e. Elsewhere both classes
are odd local units. At p≥7 the branch points of (1) are
distinct modulo p, so smooth genus-one reduction, Hasse and
Hensel give a local point and then one on the desired open.
At p=5 there is an exact remaining dichotomy when both
classes are units. If neither class is square, take a
primitive homogeneous reduction of (2). Its equations imply
L²≡βz² (mod 5), hence z≡L≡0 and then T²≡θ e² forces
T≡e≡0, impossible. If either is square the above boundary
seed suffices. Thus (1) is everywhere local at the actual
a=0 scalar (θ is square at p=5 since 5|β), independently of
all unknown θ prime support. This is not a Hasse principle.

This receiver cannot meet the *strict old* odd n≡3 (mod 4)
condition if β,θ square in Q₂, as in the original profiles.
For w=√β t of nonzero valuation, D(t) is a square in Q₂
directly, since the two factors have the same class mod 8
after stripping w² at a pole. For w a unit, put a=(1−w²)/8.
Then [D(t)]=[a(9a−1)] and (1) requires a(81a−10) square.
If a is odd, a(81a−10)≡1−2a (mod 8), never a square.
If a is even, 9a−1 is odd and odd n would require a of even
positive valuation, so a is divisible by 4. But then
v₂(81a−10)=1 and the product has odd valuation, impossible.
The excluded zero factors do not enter this calculation.
This restriction does not affect the original PointPair
interface, which does not require this retained twist class.

## 4. A uniform obstruction to e=1 on the same literal cyclic a=0 source

Keep the same original a=0,
R=4376874610839020, β=204618888056724185 and generator
P₀=(1+√2,2√2) on y²=x(x²−(3−√2)²).
For any original admissible cyclic indices h,i and defined
folded functions on this source, let

    U_j=2y([j]P₀)/(x([j]P₀)²+(3−√2)²),
    N₀=Norm(1+U_h²/R),
    Q₀=Norm(U_i)/(Norm(U_h)R¹⁵),
    W=N₀²+R Q₀²,
    c₀=12W/(1+114444R).

These are literal source formulas; the proof allows arbitrary
integer h,i for which they are defined, not just one frozen index.
At p=29, Q(√2) is unramified quadratic and P₀ has exact
order 20 in the reduction. The exact cyclic computation over
F₂₉[√2] finds U poles at 5,15 and the finite squared values
(in the basis 1,√2)

    (0,0), (8,8), (15,15), (26,14), (27,19).

At the origin the function has value zero
(equivalently U²=1/x([2]P)); the pole numerators are nonzero
in the reduction. No finite value equals −R=3 mod 29.
Thus v₂₉(N₀)≤0: either the term inside Norm is a unit,
or a negative valuation from a pole cannot cancel 1. Since
−R is nonsquare mod 29, N₀²+R Q₀² cannot cancel equal
minimal valuations: v₂₉(W)=2 min(v₂₉(N₀),v₂₉(Q₀))≤0.
The exact normalizer is ≡551=29·19 (mod 29²), so v₂₉(c₀)
is negative odd. The stripped unit of δ₀=1−βc₀² is in the
class −β, nonsquare at 29, after even negative depth 2v₂₉(c₀).
Two consequences are **uniform for this same cyclic source**:

* θ cannot be trivial, or even square in Q₂₉, under any
  alternate cyclic index with the stated inputs.
* The direct e=1 test L²=25−9βc₀² fails at 29: after
  removing the leading square 9c₀² its unit class is −β.

Moreover in any Q₂₉ solution of the *full* (2), δ₀e² must
be a unit. If it has positive depth, then β is a nonsquare
unit and βz²=1−δ₀e² would be impossible. If it has negative
depth, then L²=16+9δ₀e² has the nonsquare leading class δ₀.
Therefore a genuine multiplier must have the exact
v₂₉(e)=−v₂₉(c₀)>0, an odd valuation, not a small common unit
substitution. This is no obstruction to a general specialized
point on (2), or to the original unrestricted PointPair.

## 5. Reproducible control and scope

The arithmetic replay uses the actual a=0 constants and
a complete 20-element cyclic verification at 29. Its separate
positive toy has β=17, t=6/251, c₀=15060/68509, θ=837821881;
the replay checks the exact x-Kummer point, the twists and
both literal final cubic equations. Its b is a rational
square, not a linked original pole. No actual constant-twist
rank, rational Kummer point on that actual twist, or full
original solution is claimed.

    python3 -B replay_constant15.py | cmp - EXACT-CONSTANT15-CONTROLS.json
    sha256sum -c SHA256SUMS
