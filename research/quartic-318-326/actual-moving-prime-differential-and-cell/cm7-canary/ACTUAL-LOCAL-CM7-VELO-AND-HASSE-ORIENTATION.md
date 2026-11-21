# An independently computed ramified CM first-jet normalization

This is a small actual elliptic local canary for the first
ramified Hasse formula 93ac9e7f…. It is not one of the
large linked Heegner trace terms, a numerical q selection,
or evidence of the nonvanishing of the full weighted jet.
It checks a normalization that distinguishes Frobenius
from its negative without assuming either reduction.

Let π²=−7. Start with the rational curve
```
 E : y²=x³−(35/16)x−49/32,
 g : x³+(7/4)x²−(21/16)x−91/64.
```
Its j is −3375. The exact degree-three polynomial g divides
the standard ψ₇ and has simple roots disjoint from y=0.
The true x-doubling map sends its three roots to its three
roots (check the cleared polynomial modulo g). Each such
x is the coordinate of an order-7 point; doubling acts
with order three on its three opposite pairs. Hence
these roots are precisely the nonidentity opposite pairs
of one cyclic 7-isogeny kernel, not three unrelated
torsion labels. All assertions are replayed by rational
polynomial arithmetic.

For the normalized Vélu isogeny φ with this kernel the
three Newton sums are −7/4, 91/16, −511/64. The sums
t=∑(3x_Q²+A) and w=∑(5x_Q³+3Ax_Q+2B) over all six
kernel points are 21 and −301/4. Therefore the target
has coefficients (49A,−343B). Compose its twist
isomorphism (x′/π²,y′/π³). Its differential multiplier
is π because Vélu is normalized. The resulting map
is literally the oriented [π]: its square has
differential π²=−7, and the differential homomorphism
on characteristic-zero elliptic endomorphisms is faithful.
This also identifies the maximal ramified local action
at 7, since Z₇[π] is already the maximal local order.

Use the good Q₇(π) model
```
 C : Y²=X³+(5/16)X−π/32 ;
```
its coefficients are A/π²,B/π³, so this is the exact
same twist transport of the oriented endomorphism.
It reduces to Y²=X³−X modulo π. Let X_φ(x) be the
normalized Vélu x-coordinate over E. On C the
oriented map in these literal coordinates is
```
 X ↦ X_φ(πX)/π³,
 Y ↦ Y·X_φ′(πX)/π³ .
```
For a kernel pair with x-coordinate a the exact x
contribution is 2(3a²+A)/(x−a)+4 f(a)/(x−a)²,
where f(x)=x³+Ax+B. Summing these expressions gives
the rational X_φ verified in the checker; the Y formula
uses the true normalized differential. The checker
substitutes πX coefficientwise, uses v_π=2v₇ on Q,
strips the exact leading π-power from numerator and
denominator, and obtains
```
                      (X,Y) ↦ (X⁷,−Y⁷).
```
Thus the reduced oriented endomorphism is **minus**
Frobenius, with c=−1 in formal parameter −X/Y.
Neither this sign nor its inseparability is inferred
from the Hasse coefficient.

Separately in characteristic 7 modulo π², the Hasse
coefficient for the displayed good C is the x⁶
coefficient of (x³+(5/16)x−π/32)³, namely −3π/32≡π.
This equals πc/u with c=−1 and u=−7/7=−1, as in the
general formula. Positive Frobenius would give the
opposite first-order coefficient in the fixed chart.
This verifies the signed local normalization, not a
modular parametrization or the sign of a genus sum.

Replay (Python standard library):
```sh
python3 -B check_oriented_cm7.py | cmp - EXACT-ORIENTED-CM7-CANARY.json
sha256sum -c SHA256SUMS
```
