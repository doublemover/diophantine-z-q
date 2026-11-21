# The literal constant-15 coefficient is divisible by 16

Write \(g=g_{-23}=\sum_{D>0}c(D)q^D\) in the exact
[ramified-5 Waldspurger normalization](../../../rc-native-helper-20261120/ct-original-constant15-waldspurger-r1/FIXED-LEVEL-WALDSPURGER-FOR-THE-LITERAL-CONSTANT15-RECEIVER.md)
(SHA-256 38374b02240d1e31b8eefbf03c66b63b6b035fded686f913a604c7221b82ac4e).
For the unchanged actual scalar \(a=0,h,J\), with
\(\beta=204618888056724185\) and \(d=\beta[1-\beta c_0^2]\)
the positive squarefree twist index, we prove
\[
                              c(d)\equiv 0\pmod {16}.
\]
This evaluates neither the integer \(c(d)\) nor \(L(J_d,1)\).
In particular it proves neither vanishing nor nonvanishing of
the central value, does not bound the rank, and gives no rational witness.

## 1. A stronger mod-8 parity identity for shifted indices

The exact signed coefficient is the sum over
\(u>0,\ u\equiv z\bmod2,\ u^2+15(y^2+z^2)=23D\)
of \((u/3)\omega_{23}(u,y,z)\). Put \(b=10u+15y\bmod23\);
the second weight is \((b/23)\) if \(b\ne0\), and
\((y/23)\) otherwise. For all norm solutions the weight is invariant
under the two separate sign changes in \(y,z\). For \(y\) this
follows from
\((10u+15y)(10u-15y)=18z^2\bmod23\): if \(z\ne0\bmod23\),
the product is a nonzero square. If \(z=0\bmod23\), the two branches
have \(u=\pm10y\bmod23\) and the nonzero first argument is
\(-7y\bmod23\), with \((-7/23)=+1\); if the vector is zero
modulo 23 then both weights are zero. The \(z\) sign is immediate.

Suppose \(D\equiv17\bmod24,\ v_{11}(D)=1,\ 23\nmid D\),
with no squarefreeness requirement and no condition at 5 or 661.
Put \(n=23D\), so \(n\equiv7\bmod8\).
The inert norm obstruction \((-15/11)=-1\) excludes \(y=0\)
and \(z=0\) because \(v_{11}(n)=1\).
Also \(v_{23}(n)=1\) excludes the zero weight modulo 23, and
the weight at 3 is nonzero. Thus \(c(D)/4\bmod2\) counts
the positive \(u,y,z\) solutions. Here \(y\) is odd: if
\(u,z\) are odd their terms sum to 0 modulo 8; if they are
even their terms sum to 0 or 4.

In the odd \(u,z\) part, interchange \(y,z\) and consider
the remaining diagonal \(y=z\), i.e. \(n=u^2+30y^2\).
Every such representation has \(u,y\) odd by \(n\bmod8\).
It is a norm from \(\mathcal O_{\mathbf Q(\sqrt{-30})}
=\mathbf Z[\sqrt{-30}]\), and the positive \(u,y\) count is
one quarter of its element count (both coordinates are nonzero).
The four reduced forms of discriminant \(-120\) are
\((1,0,30),(2,0,15),(3,0,10),(5,0,6)\), so every ideal class
equals its inverse. If any inert prime has odd depth there are
no such norms. Otherwise all ideal-factor choices of norm \(n\)
have the same class: at a split prime its two prime ideals have
inverse, hence equal, classes; ramified and inert options are
unique. Both 11 and 23 split in this field, each at depth one
in \(n\). Hence if any ideal choice is principal, at least
these two independent binary choices give a factor of four
in the number of principal ideals. There are two units, so the
number of positive \(u,y\) representations is even in all cases.
The diagonal therefore contributes 0 modulo 2.

For even \(u,z\) write \(u=2r,z=2s\); then \(r\equiv s\bmod2\)
and \(n=16N((r+s\sqrt{-15})/2)+15y^2\).
Necessarily \(11\nmid y\), because otherwise the binary norm
has inert valuation one. The norm index is a nonresidue at
11 because it reduces to \(-15y^2/16\). Conversely the positive
norm representatives \(r,s>0\) in these equations give all even
\(u,z\) solutions. Define \(B^-\) to be the integral series
whose coefficients count the positive \(r,s\) norm representatives
only at indices that are nonresidues modulo 11. By the exact
[binary-theta construction and translation calculation](../original-constant15-actual-mod2-orbit-sturm-r1/ACTUAL-CONSTANT15-COEFFICIENT-DIVISIBLE-BY-EIGHT.md)
(SHA-256 9d3de8e2ea40d282d429da4249f69a3bca7c5600ec97275ee9f25040e1b95d2c),
\(B^-\) is weight 1, level \(15\cdot11^2\), character
\(\chi_{-15}\). With \(\vartheta=\sum_{j\in\mathbf Z}q^{j^2}\), set
\[
 \Psi=\frac{\vartheta(\tau)\vartheta(15\tau)-
                  \vartheta(\tau)\vartheta(60\tau)}2\ B^-(16\tau).
\]
The products in the numerator are ordinary binary theta series
of levels 60 and 240 with the same character \(\chi_{-15}\)
at common level. Thus \(\Psi\) is integral weight 2 at level 29040
with trivial character, and \([q^{23D}]\Psi\equiv c(D)/4\bmod2\)
by the above count and \(\vartheta(\tau)\equiv1\bmod2\).
The exact 12672-term [Sturm](https://doi.org/10.1007/BFb0072985)
replay establishes \(T_{23}U_{11}\Psi=0\bmod2\). Its constant
term is zero; at \(D/11\) the lower-index term of \(T_{23}\)
is zero since \(23\nmid D\). This proves \(8\mid c(D)\) under
the three stated guards alone. Independently \(c(D)=0\) if
\(D\equiv0,1\bmod3\), by the \(u\)-weight or the norm equation.

## 2. The exact literal local input at 23

Use the compact constants of the
[actual specialization](../../../joined-work-20261120/rc-linked-scalar-specialization-r1/ACTUAL-MATERIALIZED-SCALAR-SPECIALIZATION.md)
(SHA-256 28078bc4ef7af3cd784a9e54c5ad20210fa77cf0c4eba10a57c74ddcdff39b4e).
On both split arms \(\sqrt2=\pm5\bmod23\), the curves
\(y^2=x^3-(3-\sqrt2)^2x\) are good of size 24 modulo 23.
The archived \(h,i=6^{15}3^{65536}J\) are multiples of 24 and
units at 23, so the \(h\) and \(i\) points are formal on both
arms, with \(i/h=8\bmod23\). The chart
\(U=2y/(x^2+(3-\sqrt2)^2)\) has simple leading term \(-2t\)
at the origin for \(t=-x/y\). Therefore \(U_i/U_h\equiv i/h\)
on each arm, by the formal multiplication derivative. This
is the quotient before reducing, not an evaluation of \(0/0\)
([exact simple chart-zero calculation](../actual-scalar-lambda-formal-recurrence-r1/COMPRESSED-LAMBDA-CHART-ZERO-STRATUM.md),
SHA-256 b63288b00f1a4837bddb2b7f250fb68efb72860cf0af56dfce9e5e0456927b82).
The literal \(W=N^2+RQ^2\) consequently satisfies
\[
 W\equiv1+(i/h)^4/R^{29}=20,\quad
 c_0=12W/(1+114444R)\equiv1,\quad
 1-\beta c_0^2\equiv7\pmod {23},
\]
where \(R\equiv15,\ 1+114444R\equiv10,\ \beta\equiv17\).
Thus the local class of the actual \(d\) is a square unit at 23
(the scalar \(\beta(1-\beta c_0^2)\) itself is \(4\bmod23\));
this is not an assertion of a specific residue of the positive
squarefree representative.

## 3. A weight-two receiver modulo 16

Put
\[
 H=(U_{11}g)(\tau)\,\vartheta(440\tau)
      \in S_2(\Gamma_0(15840),\chi_{30})\cap\mathbf Z[[q]] .
\]
Here \(U_p\) takes the coefficient of \(q^{pn}\) at \(q^n\).
For completeness, \(g\) has classical character \(\chi_3\):
in [Sirolli–Tornaría §2 (2.1) and §9](https://arxiv.org/pdf/2107.04483)
the sole odd type-II character lies at 3, namely \(\chi_{-3}\);
changing to the classical theta automorphy factor multiplies it by
\(\chi_{-1}\) at weight \(3/2\). Its level is 180. The stated
\(\chi_3\) is even, as required by the classical weight convention.

At \(p=11\) prime to 180, \(U_p g=p^{-1}\sum_{j\bmod p}
g((\tau+j)/p)\) has level \(180p\) and character
\(\chi_3(p/\cdot)\). Indeed for
\(\gamma=\left(\begin{smallmatrix}a&b\\c&d_0\end{smallmatrix}\right)
\in\Gamma_0(180p)\), the conjugating matrices
\(A_j=\left(\begin{smallmatrix}1&j\\0&p\end{smallmatrix}\right)\)
give integral
\[
 A_j\gamma A_{j'}^{-1}
 =\begin{pmatrix}
     a+jc & (b+jd_0-(a+jc)j')/p \\
     pc & d_0-cj'
   \end{pmatrix}
\]
at the original level, with \(j'\) the unique residue making
the upper right entry integral. The residues \(j'\) are
permuted. At the corresponding argument \((\tau+j')/p\), the
linear automorphy term is \(c\tau+d_0\). For \(c>0\), the theta
multiplier ratio is \((p/d_0)\): the two bottom-right entries
agree modulo 4, 180, \(p\), and the conductor of the squareclass
of \(c\). The latter conductor divides \(c\) because \(4\mid c\).
Thus the epsilon factors and the \(c\)-part of the Kronecker
symbols agree, and the extra factor \((p/d_0)\) survives the
cube of the half-weight multiplier. For \(c=0,d_0=1\)
this is translation, and \(-I\) acts trivially in the chosen
even characters, allowing the remaining representatives.
Cusp holomorphy follows from the finite rational translates.
The factor \(\vartheta(440\tau)\) has level 1760 and character
\((440/\cdot)=(110/\cdot)\) on odd units. The four combined
half-weight factors have automorphy power
\(j^4=(c\tau+d_0)^2\); the remaining character is
\(\chi_3\chi_{11}\chi_{110}=\chi_{30}\). The claimed level
is the lcm of 1980 and 1760. No division of the integral
Fourier coefficients by 4 or 8 is used in forming \(H\).

For the actual \(d\), and indeed for any positive
\(D\equiv17\bmod24\) with \(v_{11}(D)=1\) and \((D/23)=+1\),
\[
 a_H(D/11)=c(D)+2\sum_{k>0} c(D-4840k^2)
          \equiv c(D)\pmod {16}.                       \tag{1}
\]
For every positive shift, \(4840=8\cdot11^2\cdot5\)
preserves the residue modulo 8 and valuation one at 11.
It is a nonresidue modulo 23, so cannot equal \(D/k^2\)
there; the shift stays prime to 23 including when \(23\mid k\).
If the shift is 2 modulo 3 it meets every guard of §1,
and otherwise its coefficient is zero. Terms at nonpositive
index are defined to be zero.

## 4. Exact mod-16 check at ordinary level 174240

Set \(F=(1-V_{11}U_{11})T_{17}U_5 H\), where
\(V_{11}f(\tau)=f(11\tau)\). It is weight 2 at level
\(11\cdot15840=174240\), with the same character
\(\chi_{30}\). The \(U_5,U_{11}\) are at level primes;
\(17\) is prime to the level, and \(\chi_{30}(17)=+1\).
The final factor simply replaces by zero all coefficients with
\(11\mid n\). The index is 456192, so the Sturm bound is
76032. The replay evaluates every coefficient from 1 through
76032 including the boundary. It finds
\[
                                  F=0\pmod {16}.
\]
For the modulus \(2^4\), apply the prime-ideal Sturm theorem
successively after dividing the entire form by 2 each time.
The constant term is zero. As a non-vacuity control,
\(T_{17}U_5 H\) before the \(11\) projection has 15 nonzero
coefficients modulo 16 in its original 6912-term Sturm segment.
The lift itself also gives nonzero permitted §3 values when
17 is not imposed, e.g. \(D=9185\) gives \(a_H(835)=c(D)=-8\).
This small index is not an actual source scalar.

The ternary norm checker directly evaluates the complete signed
coefficient convolution. It selects residues of \(z\) modulo
\(2\cdot11\cdot23\), includes \(y=0\) and \(z=0\) with their
exact smaller sign orbit, and admits all valuations at 11 before
the literal \(11\)-projection. For the larger \(U_5\) subsequence
all needed \(g\) indices are multiples of 5, since 440 is a
multiple of 5; the norm equation then forces \(5\mid u\).
The two Hecke terms have their exact coefficient multipliers
\(1\) and \(17\), with the latter omitted when \(17\nmid n\).
No unknown factor of the production index is used.

The actual \(d\) has \(v_5(d)=v_{11}(d)=v_{17}(d)=1\)
and \(d\equiv17\bmod24\). Set \(n=d/(5\cdot11\cdot17)\).
Then \(11\nmid n\), so the final projection leaves its
coefficient; also \(17\nmid n\), so the lower-index Hecke
term is absent. Hence \(a_F(n)=a_H(d/11)\), and (1) proves
the result. More generally this argument works for all
positive \(D\) satisfying the §3 guards, with \(5\mid D\)
and \(v_{17}(D)=1\); it makes no statement about the
normalized quotient \(c(D)/16\).

### Exact reproducible checks

    sh verify.sh

This compiles the two small C++ replays into a temporary
directory, runs the standard-library Python check, and compares
all outputs with the archived integer files.
