# A fixed-level mod-two obstruction for the actual ramified-5 coefficient

Use the exact normalized coefficient \(c_{-23}(d)\) of
[the constant-15 Waldspurger receiver](../../../rc-native-helper-20261120/ct-original-constant15-waldspurger-r1/FIXED-LEVEL-WALDSPURGER-FOR-THE-LITERAL-CONSTANT15-RECEIVER.md),
SHA 38374b02240d1e31b8eefbf03c66b63b6b035fded686f913a604c7221b82ac4e.
For the actual fixed \(a=0\) squareclass
\[
 \beta=204618888056724185=5\cdot11\cdot17\cdot163
                   \cdot661\cdot733\cdot1489\cdot1861,
 \qquad d=\beta\theta,
\]
the conclusion is
\[
                            c_{-23}(d)\equiv 0\pmod 8 .
\]
This holds without factoring or expanding the unseen part of
\(\theta=[1-\beta c_0^2]\), and uniformly for every Ready
same-\(\beta\) scalar with the donor's exact guards. It rules
out a unit in the first normalized mod-two detector
\(c_{-23}(d)/4\). It does **not** show that the integer
coefficient is zero or nonzero, nor any rank or rational point.

## 1. An exact sign orbit and the mod-two parity of its quotient

Here \(d>0\) is squarefree, \(d\equiv17\pmod{24}\), and
\(5,11,661\mid d\) to depth one. The fixed Ready class
has \((\beta/23)=-1\). Since \(\beta\) is a nonsquare unit
there, \(\delta_0=1-\beta c_0^2\) is either a unit
(if \(c_0\) is integral) or has even negative depth
(if \(c_0\) has a pole). Hence \(23\nmid\theta\) and
\(v_{23}(23d)=1\); no further cyclic arithmetic is needed.

Write \(n=23d\). The exact signed coefficient sums over
\[
 u>0,quad u\equiv z\pmod2,quad
 u^2+15(y^2+z^2)=n,qquad
 w=(u/3)\,\omega_{23}(u,y,z).
\]
It is the positive-\(u\) half of the full sum, in the
normalization of the donor. The factor \((u/3)\) is
nonzero since \(n\equiv1\pmod3\). The \(23\)-weight is
\((b/23)\) if \(b=10u+15y\) is nonzero, and \((y/23)\)
otherwise. The vector cannot be zero modulo 23, and
the isotropic fallback therefore has nonzero weight.
The weights are invariant under the signs of each
of \(y,z\):
\[
 (10u+15y)(10u-15y)\equiv18z^2\pmod{23}.
\]
For \(z\not\equiv0\), 18 is a square, so the two
nonzero \(b\)-symbols agree. For \(z\equiv0\),
\(u=\pm10y\) and \(y\not\equiv0\); on one branch
the fallback gives \((y/23)\), and after flipping
\(y\) the other branch gives \((-7y/23)=(y/23)\).
The argument is symmetric in the two branches.
Flipping \(z\) leaves the displayed weight unchanged.

There is no boundary \(y=0\) or \(z=0\): the corresponding
binary norm \(u^2+15s^2=n\) would have odd valuation
at inert 11, since \((-15/11)=-1\).
Here the ordinary elementary proof is reduction modulo
the inert prime, which forces both coordinates divisible
by 11 if the norm is divisible by 11. Likewise \(y=\pm z\)
would give \(u^2+30y^2=n\), impossible at inert 661
because \((-30/661)=-1\). Thus all the sign orbits in
\((y,z)\) have four points, and
\[
 c_{-23}(d)/4=\sum_{u,y,z>0\atop u\equiv z\ (2),\,Q=n}w\in\mathbf Z .
                                                               \tag{1}
\]
Reducing (1) modulo 2 loses the sign but no support.
Since \(n\equiv7\pmod8\), \(y\) is always odd:
if \(u,z\) are both odd then their two terms cancel
modulo 8, and if both even the even part is 0 or 4
modulo 8 and cannot account for 7 with even \(y\).
For odd \(u,z\), swap the positive \(y,z\).
It respects the parity condition and has no fixed point
by the exclusion of \(y=z\). Thus this entire part
vanishes modulo 2. It does not need a *signed* swap
identity.

For the surviving even \(u,z\), write \(u=2r,z=2s\).
The modulo-eight equality now gives \(r\equiv s\pmod2\).
Set \(K=\mathbf Q(\sqrt{-15})\) and
\(\alpha=(r+s\sqrt{-15})/2\in\mathcal O_K\). Then
\[
                 16N_K(\alpha)+15y^2=n,qquad y>0\text{ odd}.
                                                               \tag{2}
\]
If \(11\mid y\), the binary norm has valuation one
at inert 11, impossible. For \(11\nmid y\) the norm
in (2) reduces to \(-15 y^2/16\) modulo 11, a
nonresidue. Conversely every such binary norm orbit
with \(r,s>0\) counted in (2) returns a solution.
The nonresidue condition by itself excludes \(r=0\)
and \(s=0\): their positive norms have respectively
class 15 or 1, both square at 11.

## 2. A congruence to an ordinary weight-two modular form

Let \(B(\tau)=\sum_{\alpha\in\mathcal O_K}q^{N_K(\alpha)}\),
\(q=e^{2\pi i\tau}\).
This is the binary theta of
\(x^2+xy+4y^2\), discriminant \(-15\), weight 1
and character \(\chi_{-15}\) at level 15
([classical Hecke binary theta transformation](https://arxiv.org/abs/2211.14787)).
Write \(P_{11}B\) for its projection onto indices divisible by
11, and \(B\otimes\chi_{11}\) for coefficientwise multiplication
by \((\cdot/11)\). Put
\[
 B^-=\frac{B-P_{11}B-(B\otimes\chi_{11})}{8}.
\]
This is precisely \(1/4\) of the nonresidue-norm series.
Every coefficient is integral: any nonresidue has
\(r,s\ne0\), with four sign choices and one orbit
representative \(r,s>0\). The constant term vanishes.

Both operations on \(B\) are linear combinations of the
translates \(B(\tau+j/11)\), respectively by uniform
averaging and by a quadratic Gauss average. They lie at
level \(15\cdot11^2\) with unchanged \(\chi_{-15}\).
Indeed for \(\gamma=\left({a\ b\atop c\ d_0}\right)\)
in that higher \(\Gamma_0\), put
\(A_j=\left({1\ j/11\atop 0\ 1}\right)\).
The matrix \(A_j\gamma A_{j'}^{-1}\) lies on the lower
\(\Gamma_0(15)\) for \(j'\equiv j d_0^2\pmod{11}\);
its lower-right entry is still \(d_0\bmod15\).
This permutes weights without changing their
quadratic character, and cusp holomorphy persists
under the finite rational translates.

Use \(\vartheta(\tau)=\sum_{k\in\mathbf Z}q^{k^2}\), and
put
\[
 U(\tau)=\frac{\vartheta(15\tau)-\vartheta(60\tau)}2
                 =\sum_{y>0\text{ odd}}q^{15y^2},\qquad
 \Psi(\tau)=\vartheta(\tau)\,U(\tau)\,B^-(16\tau).
\]
The unary difference transforms by the ordinary theta
multiplier \(j(\gamma,\tau)\) times \((15/d_0)\)
at level 240: scaling theta by \(m\) in its standard
transformation introduces \((m/d_0)\), and 15 and 60
give the same character. Since
\(j(\gamma,\tau)^2=(-1/d_0)(c\tau+d_0)\), the characters
from the three factors multiply to
\(\chi_{-15}\chi_{15}\chi_{-1}=1\).
Thus \(\Psi\) is an honest holomorphic integral
weight-two form with trivial character at level
\[
                     16\cdot15\cdot11^2=29040 .
\]
Only a classical cusp expansion is needed at 2;
no assumption of good reduction at 2 is used.
As \(\vartheta\equiv1\pmod2\), (1)–(2) give the
exact parity relation
\[
                    c_{-23}(d)/4\equiv [q^{23d}]\Psi\pmod2 .
                                                               \tag{3}
\]

## 3. Certified Hecke annihilation at one fixed small prime

The index of \(\Gamma_0(29040)\) is 76032. The
weight-two [Sturm bound](https://doi.org/10.1007/BFb0072985)
at this level is 12672. Here \(U_5,U_{11}\) are the
ordinary weight-two operators at level primes and
\(T_{23}\) is ordinary weight-two Hecke away from
level. The included finite replay checks all
indices 1–12672 of
\[
                             T_{23}U_5U_{11}\Psi
\]
modulo 2; the constant term is zero identically.
Every one of those coefficients vanishes. The exact
coefficients used for this check compute
\([q^m]B^-\bmod2\) by the \(r,s>0\) orbit rule, then
add the genuinely positive odd \(y\)-terms in (2).
They use \(\vartheta\equiv1\) throughout, so no
large modular basis or unknown coefficients are being
approximated. For diagnostics, \(U_5U_{11}\Psi\) has
193 nonzero prefix coefficients, and
\(T_{17}U_5U_{11}\Psi\) has 10, to distinguish the
true \(T_{23}\) vanishing from zero input.
The inclusive height bound for the largest
optional prefix is \(5\cdot11\cdot17\cdot23\cdot12672\).

Sturm therefore gives
\(T_{23}U_5U_{11}\Psi\equiv0\pmod2\) as a full
\(q\)-series. At index \(d/55\), which is prime to 23,
the \(T_{23}\) coefficient formula has no lower-index term:
it is just \([q^{23d}]\Psi\).
By (3), the actual receiver coefficient is divisible by 8.
The proof only exploits the actual support \(5,11,661\)
and fixed nonsplit \(\beta\) at 23; it does not
enumerate any ternary row at index \(d\).

The method is specific to the first parity test. In
particular using \(\vartheta\equiv1\pmod2\) does not
permit the same conclusion modulo four for the half-weight
input; the signs and odd sector of (1) retain information
needed beyond this modulus. Neither nonvanishing nor
vanishing of the literal Waldspurger coefficient follows
from the congruence.

### Bounded replay

```
g++ -O3 -std=c++17 check_constant15_parity_sturm.cpp -o /tmp/constant15_sturm
/tmp/constant15_sturm | cmp - EXACT-CONSTANT15-PARITY-STURM.txt
sha256sum -c SHA256SUMS
```
The replay is exact integer parity, not a check on a toy
pole or a progressive scan in the true index.
