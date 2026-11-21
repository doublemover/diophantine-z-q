# A certified 2-adic floor for the same constant-15 coefficient

For the unchanged original \(a=0,h,J\), let
\[
 \beta=5\cdot11\cdot17\cdot163\cdot661\cdot733\cdot1489\cdot1861,
 \qquad d=\beta\theta,\qquad M=d/5 .
\]
Here \(\theta\) is the positive squarefree class of the actual
\(1-\beta c_0^2\), not a replacement discriminant. Write
\(c(d)=c_{-23}(d)\) for the exact signed Waldspurger coefficient of
[the ramified-5 receiver](../../../rc-native-helper-20261120/ct-original-constant15-waldspurger-r1/FIXED-LEVEL-WALDSPURGER-FOR-THE-LITERAL-CONSTANT15-RECEIVER.md)
(SHA-256 38374b02240d1e31b8eefbf03c66b63b6b035fded686f913a604c7221b82ac4e).
The exact lower bound, with \(v_2(0)=+\infty\), is
\[
 v_2(c(d))\ \ge\ 1+\left\lceil\frac{\omega(M)}2\right\rceil\ \ge\ 7 .
\]
Thus tests modulo \(2^k\) for \(k\le7\) all vanish on this literal
index, without evaluating its integer coefficient. Modulo 256 is
the first power of 2 not ruled out by this lower bound; no bit at
that precision is computed. This does not decide central
nonvanishing, rank, or the marked rational point.

## 1. Move the ramified prime to the fixed base

Let \(J_D:y^2=x(x+16D)(x+25D)\). Then \(J_d=J_5^{(M)}\).
The untwisted \(J_1\) has conductor 15 as in the receiver paper.
At 5 its representation is Steinberg up to unramified character;
the quadratic character of discriminant 5 is tame ramified there,
so the twist conductor exponent becomes two. At all other places
this twist is unramified. In particular \(C(J_5)=75\) and the
rational normalized newform \(f\) used below has that exact level.
The actual \(M\) is positive squarefree, \(M\equiv1\bmod4\), and
\((M,75)=1\). Indeed \(d\equiv17\bmod24\), \(v_5(d)=1\) and
\(3\nmid d\) by the exact source guards. At every \(p\mid M\)
the good point count \(N_p=(p+1-a_p(f))\) is divisible by four
because \(J_5\) has full rational 2-torsion and \(p\) is odd.
The same \(N_p\) holds for any optimal representative.

We use the **modular-symbol inequality**, not a conjectural BSD
formula. Precisely, [Zhai, Theorem 4.2 (= Theorem 1.1), proof, and
§3.2](https://arxiv.org/pdf/2102.11798v2) give at a positive twist
\(M\equiv1\bmod4\) of an optimal rational weight-two form \(f\)
at level coprime to \(M\)
\[
 v_2\!\left(\frac{\sqrt M\,L(f\otimes\chi_M,1)}{c_f}\right)
       \ \ge\ t_E(M)-1,\qquad
 t_E(M)=\#\{p\mid M:2\mid N_p\}.
 \tag{1}
\]
Here \(c_f\) is the component-normalized real period of the
period lattice of \(2\pi i f(\tau)d\tau\) on absolute homology.
The primary proof explicitly gives (1) before subtracting the
Manin constant to turn it into an elliptic-curve Néron period;
thus no Manin constant for \(J_5\) or its twists needs to be
computed. The parity description of \(t_E\) is in the paragraph
preceding Lemma 4.1. In the present case \(t_E(M)=\omega(M)\).
If the central value is zero, (1) is interpreted as \(+\infty\)
and Waldspurger already gives \(c(d)=0\).

In more detail, this step can be read entirely from Zhai's
symbol induction. Normalize the real and imaginary projections
of the \(\{0,k/m\}\) periods by \(c_f\) or \(ic_f^-\) according
to the character parity. The untwisted sum has valuation at least
\(\omega(m)-1\) by (3.4) and induction: the initial term is
\(\prod_{p\mid m}N_p\) times the base ratio, of valuation \(-1\)
as computed below, and each omitted site contributes \(1-p\).
In the character identities used in the proof of Theorem 4.2
the right side has \(2^{\omega(m)-1}\) times an integer;
each proper nontrivial divisor term gains one factor of two
for every omitted prime from \(a_p-2\chi_e(p)\). The real trivial
term, when present, is just the previous bound. Induction with
the appropriate real or imaginary period proves (1), with the
quadratic Gauss sum giving the factor \(\sqrt M\) at the positive
fundamental discriminant. No hypothesis on the cardinality of
an actual Tate–Shafarevich group enters.

## 2. Exact calibration with the full level-75 period lattice

Let \(\Lambda_f\) be the full absolute period lattice and
\(P_f>0\) the generator of \(\operatorname{Re}\Lambda_f\).
In either of the two real lattice shapes of Zhai §3.2,
\[
                              c_f=2P_f.
 \tag{2}
\]
For a rectangular lattice the primitive real period is \(P_f\)
and there are two real components; for a nonrectangular lattice
the primitive real period is \(2P_f\) and there is one component.
Thus real parts of absolute relative-symbol loops suffice to
compute \(L(f,1)/c_f\) without a choice of optimal model or
imaginary basis.

The included verifier uses the projective Manin cosets
\(\mathbb P^1(\mathbb Z/75)\), of cardinality 120. In the orientation
\([c:d]=\{g0,g\infty\}\) it imposes the usual two- and three-edge
relations and the **even** relation under complex conjugation.
At the good primes \(7,11,13\) it adds the Hecke path equations
using the \(p\) upper-triangular maps \(\tau\mapsto(\tau+j)/p\)
and \(\tau\mapsto p\tau\), with continued-fraction paths between
unimodular neighbors. The traces of the literal \(J_5\) are
\(0,-4,2\). The certificate consists of one nonzero primitive
integer nullvector checked against every row and a rank-119
minor certified by modular elimination modulo 1009. This proves
the common rational eigenspace is exactly one-dimensional.
The real part of the normalized newform's integration is nonzero:
Waldspurger at \(D=5\) has \(c(5)=2\), which is checked directly
by the signed norm formula. Hence this vector differs from
actual real integration only by a common nonzero multiplier.

For the absolute lattice, view each Manin edge as connecting
its two cusp orbits, with its primitive integer functional as
the oriented edge weight. The cusp of \(a/c\) has key
\((t,a(c/t)\bmod\gcd(t,75/t))\), \(t=\gcd(c,75)\);
the special infinity case is \((75,0)\).
These are the usual full \(\Gamma_0(75)\) cusp labels, not just
denominator labels. The labelled graph is connected. Choose
an integer potential at each vertex by integration along a
spanning tree. The edge differences from potentials are
the integrals of integral loops (and generate the values of
all such loops). The Manin edges generate integral homology
relative to the cusps and the usual boundary exact sequence
identifies absolute homology with its boundary-zero kernel.
Thus the gcd of these adjusted edge weights computes the image
of the **entire** absolute lattice under the real functional,
not just a particular congruence cycle.

The verifier finds absolute loop gcd \(8\); the primitive
integer functional on the distinguished path from infinity
to zero has value \(-8\). The sign is immaterial, as the
nullvector can be negated. We obtain
\[
 \left|\frac{L(f,1)}{P_f}\right|=1,\qquad
 v_2(L(f,1)/c_f)=-1
 \tag{3}
\]
from the real Mellin path and (2).
The continued-fraction and Hecke encoding is adapted from
[the exact level-48 symbol donor](../../../rc-native-helper-20261120/ct-original-same-pole-odd-cyclotomic-r1/level48_eigensymbol_donor.py)
(SHA-256 b238e0b036004a750f3a14be00054d1c724b199957c03824dce4f96e22442a67),
with independent level, model, even projection, cusp-cycle
normalization and finite rank certificate here.

## 3. Translate the inequality back to the literal theta coefficient

Both \(D=5\) and \(D=d\) are positive fundamental discriminants of
the same \((-,0)\) type at \((3,5)\). Their exact formula uses
the same \(k>0\) and the same ramified factor \(2\):
\[
 L(J_D,1)=2k\,c(D)^2/\sqrt D .
\]
It follows without approximating \(k\), any period, or \(M\), that
\[
 \frac{\sqrt M\,L(J_d,1)}{L(J_5,1)}
        =\frac{c(d)^2}{c(5)^2}=\frac{c(d)^2}{4}.
\]
Equations (1) and (3) give
\(2v_2(c(d))-2\ge\omega(M)\).
The seven fixed primes of \(\beta/5\), together with
\(131,6551,2470991,16782959\) from
[the exact actual \(\theta\) support proof](../actual-theta-split-scan-r1/ACTUAL-THETA-SUPPORT-AND-EXPANDED-INPUT-LOWER-BOUNDS.md)
(SHA-256 7159e6c919fd48879d6b74f021d4aefbfef7593195aa3c3fd37352d76d7a77c4),
already give \(\omega(M)\ge11\). They are distinct and no
factor of the remaining support is needed. The same source proves
existence of an unseen factor and hence \(\omega(M)\ge12\),
which is not needed for the asserted divisibility by 128 and
does not improve it alone. No equality in (1) is asserted.

### Reproduction (Python standard library only)

    python3 -B check_exact_level75_period_and_floor.py | cmp - EXACT-LEVEL75-PERIOD-AND-FLOOR.json
    sha256sum -c SHA256SUMS
