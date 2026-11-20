# A genuine one-variable marked cut for the same scalar theta

Paper draft (no Lean or rational-point claim). Given the SAME actual
prepared scalar b (in particular at a=0 or −1), let β and θ be its
original extracted squarefree parts. Choose the positive rational c,e
from βc²=b/17 and 1−βc²=θe². Write D=βc² and δ=1−D.
For the literal scalar b<1/10000, one has 0<D<1/9, β>0.
The chosen c is not a fresh θ or a new pole.

Set F1(t)=βt²−1, F9(t)=βt²−9, and

    s = (t+c)/(1+βct),
    G(t) = β(t+c)²−9(1+βct)².

Matrix determinant δ>0. Direct substitution gives

    F1(s) = δ F1(t)/(1+βct)²,
    F9(s) = G(t)/(1+βct)².

The exact marked quartic class for the small curve is
βF1(t)F9(t), and for the companion it is βF1(s)F9(s).
Thus, when t,s and all displayed factors are nonzero, the
ratio of the two squareclasses is θ if and only if G(t)/F9(t)
is a rational square. One sufficient arithmetic target is the
single curve

    C : z² = G(t) F9(t),  z≠0.

This is one cut of the full two-variable simultaneous problem,
not claimed equivalent to producing arbitrary solutions of it.
A rational point on the cut *in the below local open sets* produces
actual n and nθ with the same exact β mark. It is still
necessary to test the specified fresh-prime selector if one
needs that particular original witness schedule.

## Branch points and exact isogeny descent interface

The two F9 roots are ±3/√β. Those of G are their two preimages
under the invertible Möbius map. Neither is at infinity because
the G leading coefficient β(1−9D) is nonzero. In the variable
x=√β t, the map is x↦(x+√D)/(1+√D x).
A common root would require √D=0 (same sign), or √D=±3/5
(opposite sign). None is possible for 0<D<1/9. The smooth
projective completion is therefore genuinely genus one (four
simple branch points), not a parametrizable conic.

Set k=z/F9(t), so G(t)=k²F9(t). The literal quadratic in t is

    A_k t² −16βct + (D−9+9k²)=0,
    A_k = β(1−9D−k²).

With H=A_k t−8βc, its discriminant divided by 4 becomes

    H² = β(9k⁴+(82D−18)k²+9δ²)
       = 9β(k²−δ)² + (8βck)².

If A_k≠0 the reverse formula is t=(H+8βc)/A_k;
when A_k=0 the degree drops to the explicit linear equation.
At k=0, t at a branch, or 1+βct=0, handle or exclude the
finite exceptional coordinates before drawing a conclusion.

Putting X=9βk², Y=9βkH gives the ordinary elliptic curve

    E_c : Y² = X(X² + aX + b_c),
    a = β(82D−18),    b_c = 81β²δ²,
    a²−4b_c = 256β²D(25D−9) ≠ 0.

The affine even quartic is exactly the x-class-β torsor of the
2-isogeny descent. Conversely a point of E_c with nonzero
X=βr² gives k=r/3 and H=Y/(9βk), with the displayed t recovered
on the same open set. Its 2-isogenous companion has equation
Y²=X(X−64βD)(X−4β(25D−9)); the positive root 64βD=(8βc)² is a
square. None of this identifies the actual marked torsor class
with zero globally.

## Local admissibility, a=0 or any such β divisible by 5

For leading tests at 2,3, β satisfies β≡17 mod24 and θ≡1 mod24.
The prepared squares imply v₂(c)≥2 and v₃(c)≥1.
The following give nonempty local OPEN sets, not a chosen
global rational point on C.

* **Real:** Take t sufficiently large and positive. Then s tends
  to 1/(βc)>3/√β because D<1/9. Both F1,F9 are positive
  for both parameters, G/F9>0, and the norm equation locally
  has a nonzero real square root.
* **2:** Pick t with w=√βt a unit and w²−1=2^a u where
  a≥5 is odd and u≡1 mod4 (e.g. a=5,u=1; its squared target
  1+2^a u is 1 mod8). Then F1(t) has valuation a, F9(t) has
  exact 3 and F9(t)/8≡−1 mod4. Thus βF1(t)F9(t) has even
  valuation and odd residual unit ≡3 mod4, as required.
  Because v₂(c)≥2 and t is a unit, 1+βct is a unit. The exact
  discrepancy is
       G−F9 = βc²(1−9βt²)−16βct.
  Its two terms have valuations at least 7 and 6, respectively.
  Dividing by F9 leaves v₂≥3, so G/F9≡1 mod8 and is a square.
  The two small/companion squareclasses agree locally since
  δ is a square here. All conditions persist in a neighborhood.
* **3:** Choose v₃(t)<0. Since v₃(c)≥1, the numerator t+c has
  valuation v₃(t); if the denominator is a nonunit its valuation
  is either v₃(c)+v₃(t)<0 or a nonnegative cancellation value.
  In all cases s also has negative valuation (avoid the single
  zero denominator). For each parameter q=t,s, divide F9(q)
  by β q²: the resulting unit is 1 mod3, so F9(s)/F9(t)
  and hence G/F9 are squares locally. Removing squares from
  βF1(q)F9(q) yields an odd-to-3 class with unit residue 2:
  both F1,F9 have leading βq² and both residual units 1 mod3.
* **p dividing β:** Here p≥5, c is integral: βc²=b/17 has
  positive valuation (including p=17). An integral t gives s
  integral, denominator unit and F1,F9 units. In fact t=0
  gives ratio 1−D/9≡1 modp, so a nearby nonzero t works.
  The small squareclass then contains p to exponent one as
  required. At a=0 one has 5|β, so this covers p=5.
* **p≥7 dividing δ, with D integral and unit:** Here β is
  a square mod p and c a unit. Put x=√βt mod p, avoiding
  ±1,±3. Then s≡c modulo p and
  χ(G/F9)=χ(−8)χ(x²−9). There is an x making this +1.
  At p=7 take x=0. At p≥11 use the exact identity
  Σ_x χ(x²−9)=−1 (factor the two difference-of-squares
  variables); among all nonzero values there are (p−3)/2
  squares and (p−1)/2 nonsquares, and removing x=±1 loses
  at most two in the desired class. Both small F1,F9 are
  units, so in particular n does not contain any p dividing θ.
  If p=5 divides θ this *unit method* does not work, but it
  isn't needed for a=0. Even-positive valuations are not
  excluded by this failure of the unit method.
* **p≥7, c integral, D≡9/25 mod p:** This case necessarily
  has β and c units, β square mod p, and δ a unit. Exactly
  one of the two F9 roots is shared with G (the opposite-sign
  branch condition √D=±3/5 in the residue field); the other
  factors are distinct. G/F9 after cancellation is a
  nonconstant Möbius bijection on P¹(F_p). Among preimages
  of its (p−1)/2 nonzero squares, exclude the canceled root
  and infinity, so a finite ordinary preimage remains.
  The argument allows the uncanceled G root at infinity,
  as can happen for p=7.
* **p≥7, negative v_p(c):** β is a unit, as its own support
  has c integral. Multiply G by c⁻², a square scaling:
  the reduced quartic has simple branch equations
  βt²=9 and βt²=1/9 with no coincidences for p≥7.
  This is good genus-one reduction. Such a curve over F_p
  has a point by Hasse's bound, which lifts, and the local
  point can move away from the finitely many excluded t's.
* **Other p≥7:** if D vanishes mod p use the ratio at t=0
  and deform. Otherwise the only possible coincidences of
  the branch sets are δ=0 (Möbius determinant zero) or
  D=9/25, already handled. The binary quartic has good
  genus-one reduction, including a single simple root at
  infinity if its leading coefficient vanishes, so the
  same lifting argument applies.

Thus this cut is everywhere locally soluble for the actual
a=0 scalar β (and any prepared β divisible by 5). The open
sets simultaneously retain β⊂supp(n), no θ-support in n,
n odd with n≡3 mod4, and n≡2 mod3, whenever a single **global**
t,z can be chosen there. Local solubility alone does not choose
such a point: this is a 2-isogeny Selmer class, and its
global rationality/possible Sha obstruction is a genuinely
separate requirement. No congruence check generates the same
actual h or θ.
