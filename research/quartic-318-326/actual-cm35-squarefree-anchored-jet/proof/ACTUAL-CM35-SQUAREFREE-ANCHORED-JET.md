# A sparse nonzero ramified jet on the genuine squarefree-level-33 newform

This is a separate, more representative pilot than the
level-32 CM15 test. It uses the actual genus-three curve
X₀(33), the genuine level-33 rational newform, actual
maximal-order discriminant −35, and the ramified prime 5.
The signed whole-class jet is proved **nonzero**, without
a model of the modular map or reconstruction of its
eigenline. The positive certificate consists of four
outgoing T₂ rows and four weighted Atkin rows touching
nine residue vertices, and a separately proved nonzero
anchor. No `f` value in a numerical eigenspace is assumed.
This is still not a statement about any selected
production curve of conductor 205042530.

## 1. The genuine newform, conductor and phase

Let E be the rational isogeny class of
`y²+xy=x³+x²−11x`. Its integral discriminant is
88209=3⁶·11² and c₄=553 is a unit at both primes,
so the conductor is exactly 33. The class is
[33a](https://www.lmfdb.org/EllipticCurve/Q/33a/);
its rational newform is fixed by modularity and the
primitive q coefficient a₁=1. We can use the
actual optimal quotient Eopt instead of needing
a precise isomorphism with a chosen minimal model.
The point counts (at 3 and 11 include the node)
are 2 at 2, 5 at 3, and 11 at 11. Thus a₂=1,
a₃=−1 and a₁₁=+1, so the eigenvalues of w₃,w₁₁
on the normalized new differential are +1,−1
respectively. The full Fricke sign is −1.

The two reduced form classes of Δ=−35 are
[1,1,9] and [3,1,3]. Both 3 and 11 split, the
class of a prime above 3 is nontrivial (there
is no element of norm 3), and its square is
principal. The absolute genus extension is
H=Q(√5,√−7); the two quadratic discriminants
5,−7 are coprime and their product is −35,
so this is the Hilbert class field of the
quadratic subfield K=Q(√−35). The genus
character ψ cut out by √5 is − on the
3-ideal and + on the 11-ideal. Both level
markings are conductor one. The conductor-one
oriented CM reciprocity gives the two labels
below in one class orbit. Complex conjugation
duals the level via full Fricke and shifts by
the level ideal, of ψ-value −. This cancels
the full Fricke differential sign; any fixed
cusp translation cancels in the signed
difference. Thus the actual based Heegner
trace belongs to the anti-invariant part over
Q(√5), not over Q(√−7). This is the same
phase mechanism as in the lower semistable
production donor but checked explicitly here.

## 2. The actual oriented reduced endomorphism and marked level

Use k=F₅(z), z²=2, E₀:y²=x³+1. Its F₅ trace
is zero (the cube map is a bijection on F₅),
so its square Frobenius over k is [−5].
All E₀[2] and E₀[3] are k-rational.
The same holds for each of its normalized
prime-to-5 isogenous models over k.

Choose the exact two consecutive order-three
kernel x-coordinates 1 and 4+z. The first
short Vélu quotient has coefficient B=3,
the second B=4 (A remains zero). The
second kernel is not the dual of the first.
The normalized composite followed by the
scale divided by s²,s³ with s=3∈F₅ makes
an actual endomorphism γ of degree nine
with differential s=1/2. It is cyclic
because no backtrack occurred. Its dual
has differential 9/s, so its integral
trace is 1 modulo 5. The degree bound
leaves only traces −4,1,6; the columns
(1,1),(1,0) of its actual action on the
two chosen E₀[2] generators have odd
trace, forcing integral trace 1.
Then the discriminant of Z[γ] is the
fundamental −35 and α=2γ−1 is the
chosen oriented √−35 endomorphism.
The cyclic degree-nine kernel is the
square of the chosen prime above 3.

The degree-eleven endomorphism γ+1
has norm 11 and kernel defining the
actual oriented C₁₁, not an arbitrary
lookup by j. If x(γ P)=A(x)/B(x) then
`y(γP)/y(P)=(A′B−AB′)/(s B²)`
by preservation of the differential
up to s. Therefore its kernel x
polynomial of degree five is the
gcd of A−xB and A′B−AB′+sB².
The exact common polynomial has coefficients
ordered constant first:

    (4z, 2+3z, 1, 3, 4+2z, 1).

It is separable and coprime to the denominators.
This uses the sign equation for γP=−P.
The opposite 11 line is similarly ker(2−γ),
from γP=[2]P with matching signed ratio;
the checker strips the irrelevant singular
x equality when applicable. Both true
11 lines are available without enumerating
the 11-torsion splitting field. The first
CM label is the pair with C₃ the first
kernel of the γ chain. The second one is
the actual quotient by that C₃, transporting
C₁₁, and with C₃ the next kernel of the
same horizontal chain. These are the two
different exact classes, not separately
chosen uncorrelated orientations.

The oriented maximal-order lift exists by
[Gross, Proposition 2.1](https://archive.mpim-bonn.mpg.de/id/eprint/3578/1/preprint_1985_30.pdf),
with the specified action on Lie and the same
prime-to-5 étale marking. The O_K action is
maximal because its discriminant is fundamental.
Write ε=√5 and choose the local unramified
√−7 reducing to 2z. Then α acts on Lie by
ε√−7. The oriented ramified first term can
be recovered from this **same** residue
endomorphism, without guessing its sign.

For an odd normalized Vélu map with
X-coordinate (x+t/x+O(x^{-2})),
its y-coordinate is (y) times the
derivative of the X-map and its
formal (Z=-x/y) coefficient is
(Z+2tZ^5+O(Z^7)). For one 3-line
(t=2(3r^2+A)), with r its one
kernel x value. The j=0 formal law
is plain addition through degree 5:
sixth-root scaling forbids any other
total degree below 7. With the final
scale s=1/2 and α=2γ−1 this gives

    [α](Z) = c Z⁵ + higher,    c=2(t₁+t₂)=3+z.

As a check c^(5+1)=2, the coefficient
of [−35]=[−7][5] since [5] begins with
−Z²⁵. The second label under the
normalized 3-isogeny has the same
coefficient before reformatting;
the canonical frame scales it by
(u^{1-5}), where u is the
differential of that isomorphism.
The original same-orientation degree
5 jet identity gives `dHa(v)=c·√(−7)/(−7)`. The Hasse
invariant of the short model with
B=1 is 2A at p=5, and Kodaira–Spencer
converts the frame to (dA/6),
as verified in the CM15 Hecke pilot.
Thus the literal signed normalized
weight-two first jet after both frame
scales is

    L=(4+z)e₇+(4+4z)e₅.

The indices 7,5 refer to the
same two exact CM points in that
weighted order. A single fixed
prime-to-5 scalar (including
multiplication by 4) converts
L into the actual Néron jet.
The Manin factor is one for
the semistable optimal quotient
by [Česnavičius](https://arxiv.org/pdf/1703.02951v3).

## 3. Eight exact rows and a geometric anchor

For a nonzero tame cyclic-subgroup
map into the chosen short model
changing invariant differential by u,
the T₂ row transports weight two
by u²/2 per directed arrow, and
the W_j row by u²/j on its one
marked Frobenius-independent arrow.
To compute a 2-arrow we use the
actual 2-kernel r and the normalized map
(xmapsto x+(3r^2+A)/(x-r)).
Each marked subgroup is its true
image, not selected merely by target
degree. To image its exact monic
kernel polynomial P under a rational
map R, compute (Rpmod P) then
find the degree-five minimal
polynomial of this image element
in (k[x]/P). These images are
separable because all arrows used for
transport have degree prime to
the marked subgroup order. For
a W₁₁ arrow one instead sends any
different actual 11-line to the
dual 11-line and carries the true
C₃ by the same map; W₃ operates
analogously. The normalized Vélu
X-map from the kernel polynomial is
[
x+4f((P'/P)^2-P''/P)-2f'(P'/P)+2d,x-2t,
]
where (f=x^3+A x+B, d=deg P,t=-[x^{d-1}]P); it is obtained by
summing (4f(r)/(x-r)^2+2f'(r)/(x-r))
over kernel x-values r. The replay
checks the W₁₁ action at the actual
CM point independently against the
opposite explicit kernel of 2−γ.

The initial field models and all
chosen quotient signs live over k,
and the replay canonically names
vertices by the normalized C₃ x
and ordered degree-five C₁₁
coefficients. The full naming
roster has 16 vertices (it is
not used to solve an eigenline).
For the needed relation write R_i
for the stored exact row of T₂−1,
S_{j,i} for the stored exact row
of W_j−its eigenvalue. Direct
coefficient comparison gives

    L − z e₀ =
          3z R₀ + (4+4z) R₅ + (2+2z) R₉ + (3+z) R₁₅
        + (3+2z) S_{3,0} + (1+z) S_{3,7}
        + (1+3z) S_{3,8} + (4+4z) S_{11,2}.

It touches only vertices
0,1,2,5,7,8,9,12,15.
There is no requirement for all
these destinations to be outgoing
row sources: every displayed row
itself has all its true arrows.

The orbit of anchor vertex 0
under the actual W₃,W₁₁ and
residue 5-Frobenius has the eight
distinct vertices
0,1,2,3,8,9,10,11, checked via
the same literal subgroup transport.
The normalized form is over F₅,
so zero propagates under Frobenius,
and its Atkin eigenrelations
transport a zero to a zero.
But X₀(33) has genus 3 (index 48,
4 cusps, no elliptic exceptions),
smooth proper at 5, and a nonzero
holomorphic differential has only
4 zeros counted with multiplicity.
Thus its true value at 0 is nonzero,
without ever computing that value.
The eight-row identity forces
`L(f₃₃)=z·f₃₃(0)≠0`.
This proof does not need a dense
eigenspace rank, an actual q-expansion
value beyond a₁=1, or computed
complex CM coordinates.

In particular this is an actual
ramified jet of the true alternating
two-term genus trace at this LOW
pilot. Its [4] form in the literal
5-twist has nonzero component-zero
additive residue; no rational
5-torsion exists since at the
independent good prime 7 the
twisted count is 12. Hence the
pilot trace is nontorsion. A true
anchor on this small curve is
not evidence for an actual
production anchor at level
205042530: the same zero bound
there is much larger, and an
Atkin–Frobenius orbit of one
point need not suffice. Neither
production's exact p-data nor
any high-level old/nonold
eigenspace comparison is assumed.

Replay, standard Python:

    python3 -B check_cm35_anchored_weighted_jet.py | cmp - EXACT-CM35-ANCHORED-JET.json
    sha256sum -c SHA256SUMS
