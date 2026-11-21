# Exact first Cassels forms and the next actual mark bit at conductor 15

Use the exact same pair
E_d:y²=x(x+16d)(x+25d), E′_d:y²=x(x−d)(x−81d)
and signed dual 2-isogenies φ:E_d→E′_d, ψ:E′_d→E_d.
The φ scalar Selmer group is measured by x on E′_d, the ψ
group by x on E_d. As before d>0 is squarefree, d≡17 mod24.
For the literal a=0 scalar write β for its known first class,
δ₀=1−βc₀² for the raw folded coefficient and θ=[δ₀].
Then 5|β, (β,θ)=1, d=βθ. The named mark is θ in the
φ-rational image on E′_d. No actual mark or rank is claimed
below. The finite arithmetic includes one genuine positive
rank-one *numerical* Ready example that is not a linked source.

Bits in the following formulas lie in F₂; a negative
quadratic Hilbert symbol represents the bit 1.

## 1. Literal pushouts and both first scalar forms

Use [Fisher, Higher descents, §3 and Theorem 2.1](https://www.dpmms.cam.ac.uk/~taf1000/papers/higherdesc.pdf).
For a ψ-cover of E_d the target function x+16d pulls back
to a pushout for the rational ψ-kernel on its Jacobian
E′_d: the half-divisor on E_d is T_{−16d}−O, and its
pullback in Pic⁰ is dual φ(T_{−16d})=T₀. For a φ-cover of
E′_d the analogous function is x−d, since ψ(T_d)=T₀.
The identity is on the actual Picard classes; it does not
use equality of representatives or a change of isogeny.
Fisher’s formula evaluates the Hilbert symbol of this
actual pushout at a local point against the second scalar
class. A constant scaling has product 1. Points on a root
or at infinity used below may be perturbed in the open
Kummer coset; evaluation is made at nonzeros and nonpoles.

For e,f in the ψ Selmer group:

* At ramified odd p|d the local class is 1 or −d. Near O
  the pushout is square. For class −d use T_{−25d}, where
  x+16d=−9d, of the same class.
* At 2 use the good model with x=4X and take odd X in the
  desired class e; all such X lift. Then x+16d has class
  X+4d, which agrees with X modulo 4. The Hilbert symbol
  against the unit f only sees these mod-4 signs.
* At 3 ψ is locally trivial. At infinity the sign of the
  pushout on the negative component is the same as x; on
  the positive component both are positive.
* At 5 prime to d with d nonsquare, both classes are units,
  and one can again use T_{−25d} for the nonsquare unit.
* At 5 prime to d with d square, scale to d=1. The two
  local generators can be represented by x=5 and x=50,
  where x+16=21 and 66 are squares in Q₅. Since x+16 is the
  full-root Kummer character on E_d, sums of these points
  give the same square property for all scalar classes.
* At other good odd places e,f are units. If x+16d is
  close to zero, the other two cubic factors are units,
  so its valuation is even. At a pole the leading x³
  gives even x-depth as well. Thus the local symbol is 1.

Consequently the pushout symbol agrees with (e,f)_v
at every place except possibly 5 in the augmented case
(5∤d and (d/5)=+), where the pushout symbol is 1.
Global Hilbert reciprocity gives the **entire ψ self-pairing**

    CT_ψ(e,f) = (e,f)_5 in the augmented case, and +1 otherwise.

In the augmented case this form is nonzero exactly when
Sel^ψ maps onto all four Q₅ squareclasses; no arbitrary local
test from a class not in the global Selmer group is used.
In the transpose-matrix notation, with k=ℓ+r, the test is
k∈im(Aᵀ) and ℓ∉im(A). Indeed the first criterion gives
a Selmer representative with 5-exponent one, and the
second gives a representative with 5-exponent zero and
nonsquare stripped unit. This gives the exact one-bit
rank-one gate at minimal dimensions (2,3).

For e,f in the φ Selmer group, use x−d. At an odd p|d
the nontrivial case is class d: use T_{81d}, where x−d=80d.
If p≠5 its local symbol against d is (−5/p); if p=5|d,
write d=5d₀ and 80d=5²·16d₀, giving (d₀/5).
At 2 the generator 5 can be represented on the normalized
E′ by x=5, giving x−1=4 square. At 3 the two generators
from x=81d and x=3 give respectively 80d and 3−d,
both square units; add them using the full-root character.
At real no negative scalar class occurs. At other good
places the same even-depth argument applies. At 5∤d with
d nonsquare, both classes are units and x=81d has
x−d=80d of odd valuation, so the contribution is − exactly
when *both* are locally nonsquare. With d square at
unramified 5 the φ-image is trivial. This yields the full
φ self-form as a diagonal support sum with these explicit
coefficients and the one nonsquare-unit term at 5.

## 2. Actual θ first bit, visible support, and conditional full one-hidden row

In the literal branch 5|β, the rational torsion class d
is zero for the pairing, so θ and β give the same test.
The exact fixed coefficients of CT_φ(θ,f) are **the parity
of f’s valuation at {5,11,17,733}**, all in the known β.
For the ramified 5 coefficient use the stripped d/5;
θ is square there, hence this bit equals that of β/5.
This part does not need a factorization of θ.

There are four independently certified odd θ factors
131,6551,2470991,16782959; the exact stripped d-unit bits
at these primes and at the eight β primes are inherited
from the compact actual scalar replay. Using just their
rows and the 2-phase, exhaust all 2¹² masks supported on
the visible primes (and the determined 3 bit). Only 1 and
β survive even these necessary rows, so a first-bit
obstruction class must have support at an unseen θ prime.
We do not assert that the listed primes are all of θ.

If θ has exactly one unseen prime H, then H≡1 mod4 and
H≡1 mod3 from the full θ and visible product; H splits
5 since θ is square at 5 and the product of its four known
factors is square there. The classes (H/p) at the visible
primes are recovered by subtracting their visible Legendre
row sums from the *true* stripped d-unit bits; reverse
entries agree by reciprocity since H≡1 mod4. This is the
same conditional-one-unseen aggregate construction with
the new scalar φ/ψ matrices. It gives

    Sel^φ={1,β,θ,d},    Sel^ψ={1,e,−d e,−d},
    e=5·11·17·1489·131·6551·2470991=2952271997968816765.

Thus both first self-pairings are zero in that conditional
case (the ψ form is unaugmented irrespective of hidden
count). This is not a rational point or a rank. No count
of unseen primes is inferred from the computation.

## 3. Actual named 2-lift and its cross bit

For the φ class θ on the literal scalar, take the named
second squareclass κ=θ for the pushout x−d. At p|θ the
twist class of the pushout at x=81d is 5d. Comparing κ=θ
to this, β is already square there; the remaining ratio
has class 5. The opposite local group is {1,−d}, whose
only unit class is 1. Thus this named lift is admissible
iff every p|θ splits √5; all other rows follow from θ
being square at 2,3 and at β, and from the good unit
images. This condition is equivalent to θ a global
√5-norm: the only odd ramified field prime is 5, where θ
is square, and the joint Hasse norm test for this quadratic
field is exactly the absence of inert odd support.
It is the precise old Γ norm condition, not a claim that
a norm is known. In the one-unseen situation of §2 it
does hold.

Use the raw d_raw=βδ₀, which is square-equivalent to d.
The actual named full 2-Kummer triple on E′ is
(θ,θ,1), with literal intersection, after rescaling,

    C₂: X²−Y²=β T²,       X²−81β T²=δ₀ Z².

The second conic has the explicit rational point
(X,T,Z)=(1,c₀/9,1), the first has (X,Y,T)=(1,1,0).
Their tangent linear forms on C₂ are

    L₂=X−9βc₀T−δ₀Z,      L₃=X−Y.

The half-divisor of L₂L₃/T² represents T₀ on its Jacobian
E′. To see the orientation, use the four geometric points
at T=0, with X=1 and Y,√δ₀ Z independently ±1. Forgetting
Y or Z gives the two degree-two conic projections.
Each tangent is double its conic point, so its half-divisor
is the corresponding degree-two fibre. With one common
point at infinity, these fibres differ by the two points
obtained by flipping Y and Z respectively. In the split
2-Kummer covering each T_i flips the other two root
signs; on this infinity fibre projective common negation
identifies that with flipping the ith sign. So these
differences are T_d and T_{81d}; their difference is T₀.
Subtracting the hyperplane gives the stated
half-divisor. Thus Fisher’s cross pairing, with α₂ the
displayed lift and e a ψ scalar class in S₂, is the
product of (L₂L₃,e)_v on the actual local C₂ points.
It is independent of the choice of lift modulo the
first radicals by Fisher’s Theorem 2.1. In particular a
rational original θ-mark would make the bit trivial.

Here take the exact positive e from §2 and assume it really
belongs to Sel^ψ (automatic under the exact one-unseen
hypothesis; otherwise this is a separate admission).
It is in S₂^ψ since the actual ψ self-pairing is identically
zero. We compute as follows.

* At β primes take T=0, X=1, Y=−1,
  Z=−1/√δ₀, with √δ₀≡1 (mod p). The tangent product
  2(1+√δ₀) is square at these odd places, including 5.
  At 2 the same choice with √δ₀≡1 mod8, possible by
  the actual v₂(c₀)=2, makes the stripped tangent
  product 1 mod4, so it pairs trivially with the odd e.
  At 3 e is itself square.
* At p|θ where e is ramified, take T=1,Z=0,
  X=9s, Y=±4s√5, s=√β with sc₀≡−1 modp.
  Then L₂≡18s and
  L₃=s(9∓4√5). The latter parenthesis is
  (2∓√5)², so the unit sign is (2/p). The three
  actual test support primes here are 131,6551,2470991,
  whose signs multiply to −. At every other p|θ the
  admitted e is a unit and therefore a square in the
  ψ local group. The infinite place is neutral.
* At remaining odd primes a primitive locally-good conic
  tangent has even evaluation depth: put its primitive
  isotropic point into a Witt basis with unit hyperbolic
  pairing. The conic becomes a UV+bW² form with a,b
  units and tangent V; for a primitive isotropic point
  with v(V)>0, U is a unit and v(V)=2v(W).
  Projections of primitive C₂ coordinates to either
  conic are primitive, by the omitted square equation.
  This also applies after stripping any even positive
  depth of δ₀ in Z: the tangent point on the normalized
  conic remains primitive and there is no scale change
  in the tangent line.
* If p is a pole of c₀, put h=−v_p(c₀)>0,
  c*=p^h c₀, δ*=p^{2h}δ₀, and Z=p^h Z*.
  Here β and δ* are units, and the second conic has
  primitive point (p^h,c*/9,1). The actual tangent L₂
  is p^(−h) times this good normalized tangent, so
  exactly the factor (p^h,e)_p remains. L₃ has even
  depth on the first conic. No p in e’s support
  overlaps a c₀ pole.

By Hilbert reciprocity, since e>0 and e≡1 mod4 and
the reduced denominator D(c₀) is odd and prime to e,
the product of these pole factors is the Jacobi
(D(c₀)/e). We conclude that the **second cross sign**
is exactly

    Θ₂(θ,e) = −(D(c₀)/e) = −(D_exc/e).

The last equality uses the actual four fixed odd
denominator primes 29,181,1346909,70850399941, whose
character factors are +,−,+,− respectively. The
remaining squarefree odd denominator part D_exc is
exactly the crossed-source part; this e is the already
defined first conductor in the independent factor-free
crossed-denominator method. No new enormous factorization
is needed, but the existing crossed Jacobi value is
uncomputed. In particular if one hidden prime is proved
and the precise crossed sign is +, the constant-15 mark
is obstructed at the next lift. If the sign is − this
test is neutral. Neither outcome is currently asserted.

## 4. Positive numerical rank-one control

For β=17·2857 and t=60/119009, put
c₀=10t/(1+9βt²) and the resulting raw δ₀=1−βc₀².
The positive b=17βc₀² has square denominator and
the required local square depths 6,2,2 at 2,3,17.
Its θ is 13·163·199·13988293681, obtained by the exact
rational factor identity in t. The earlier back-map
gives the exact nontrivial rational mark. This augmented
sign-minus example has scalar dimensions (2,3). Its two
actual ψ Selmer classes −10595 and −17 have 5-local classes
5 and a nonsquare unit, so their computed ψ sign is −.
Thus rational ψ-image dimension is one while rational
φ-image dimension is two. The exact dual-isogeny index
identity gives **rank one** over Q, with no analytic
hypothesis or parity converse. This is a numerical Ready
control, not a linked original pole. In particular the
minimal augmented CT gate is genuinely realizable.

    python3 -B replay_scalar_cassels.py | cmp - EXACT-SCALAR-CASSELS-CONTROLS.json
    sha256sum -c SHA256SUMS
