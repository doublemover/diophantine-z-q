# The moving ramified jet uses the fixed weight-two differential

This uses the **same** selected marked same-scale family,
the reviewed lower semistable \(E^\flat\) and auxiliary \(h'=-2207\),
and the original selected contacts. It does not solve the
finite orbit sum or find new selected primes. It replaces
the need to construct a characteristic-zero point-valued
parametrization at the mover by one exact finite modular
differential read per oriented residue label.

## 1. A common unit at every actual mover

The lower curve is \(E^\flat:y^2=x(x+76768)(x-407)\) of
squarefree conductor \(N=205042530\). Fix the connected optimal
elliptic quotient of \(J_0(N)\) and then use a **primitive rational
isogeny** into this actual curve, based at the cusp at infinity.
A primitive isogeny may be taken by removing rational scalar
factors. Its kernel is cyclic: a noncyclic primary part would
contain the full two-dimensional \(\ell\)-torsion, and one could
factor out \([\ell]\). Any prime dividing its degree therefore
gives a rational prime-degree isogeny. Already
[Mazur, Theorem 1](https://www.math.columbia.edu/~goldfeld/Mazur-Goldfeld1978.pdf#page=2)
bounds all such primes by 163. In this semistable case
the same paper, Theorem 4, gives surjectivity of the residual
representation for primes \(>11\), so the degree in fact
has no prime factor \(>11\). The weaker 163 bound is sufficient.

Let \(f_N\) be the fixed normalized weight-two newform of
\(E^\flat\), with \(a_1=1\). For the optimal quotient,
[Česnavičius, Theorem 2.11](https://arxiv.org/pdf/1703.02951#page=8)
gives \(c_{\mathrm{opt}}=\pm1\) in the equality of the
Néron differential pullback with \(f_N(q)dq/q\).
At each actual mover \(p>76176\), all models have good reduction.
The primitive isogeny and its dual extend to the good models,
and the product of their differential factors is its degree,
a \(p\)-adic unit. Their separate factors are integral, hence
both units. Consequently on the actual modular model at \(p\),
\[
      (\pi^\flat)^*\omega_p=u_p\,\omega(f_N),
       \qquad u_p\in\mathbb Z_p^\times .
\]
The sign/scale \(u_p\bmod p\) is **common to the whole trace**.
It can be discarded for a nonzero test, not for reproducing
the exact signed value in fixed point coordinates. Arbitrarily
postcomposing by multiplication by a mover prime would spoil
this conclusion; the primitive normalization matters.

## 2. The literal fixed level and the finite oriented formula

Write \(r=976393\), \(d'=rD\), and \(\Delta=h'd'\) as in the
fixed lower genus detector. Let \(p\mid D\) be one of the actual
simple-prime factors, so \(p\nmid N\) and \(v_p(\Delta)=1\).
In a fixed ramified local genus field use
\(\epsilon=\sqrt{d'}\) as uniformizer, with the sign from the
chosen local embedding. The full genus character \(\psi\)
and every \(C_N\) remain those of the original lower orbit,
with no new choice of phase in individual summands.

To compute at a residue label \(a\), choose a fine
prime-to-\(p\) Legendre chart over a finite unramified extension
and preserve the existing marked cyclic subgroup. Use
\[
  B_\lambda:y^2=x(x-1)(x-\lambda),\qquad
  \eta=\frac{dx}{2y}
\]
for the local Hodge trivialization. The marked modular value
\(f_N(B_\lambda,C_N;\eta)\) is the Katz weight-two value:
it depends on \(C_N\), not just on \(\lambda\) or \(j\).
In this differential the Hasse scalar is
\[
 H_p(\lambda)=(-1)^{(p-1)/2}
      \sum_{j=0}^{(p-1)/2}\binom{(p-1)/2}{j}^{\,2}\lambda^j .
\]
It is the \(x^{p-1}\) coefficient in the Legendre cubic to
power \((p-1)/2\); at a supersingular point
\(H_p'(\lambda)\) is nonzero. The Kodaira–Spencer normalization
matching \(dq/q\) on the Tate curve gives
\[
 \omega(f_N)=
  f_N(B_\lambda,C_N;\eta)\,\frac{d\lambda}{2\lambda(\lambda-1)} .
\]
For a direct factor check put \(Y=y/(x-\lambda)\). Then
\[
 dY=
 \left[x-\lambda-\frac{\lambda(\lambda-1)}{x-\lambda}\right]\eta,
 \quad
 \partial_\lambda\eta=\frac{\eta}{2(x-\lambda)} .
\]
The coefficient of \(x\eta\) in the de Rham variation is
\(1/(2\lambda(\lambda-1))\). The residue pairing of \(\eta\)
and \(x\eta\) is \(+1\) with the convention whose Tate
normalization sends the square of \(du/u\) to \(dq/q\).
The sign can also be fixed directly at \(\lambda=0\):
the nodal coordinate \(t=y/x\) gives
\(\eta=dt/(t^2+1)=(1/(2i))\,d\log((t-i)/(t+i))\);
the cusp has width two, so the leading coefficient is
\(-d\lambda/(2\lambda)\) as in the displayed formula.

Let \(c_a\) be the first nonzero coefficient, at degree
\(p\), of the reduced **oriented** endomorphism
\(\sqrt{\Delta}\) in a parameter with cotangent \(\eta\).
This is the literal orientation from the ramified CM jet
calculation in Joined 93ac9e7f, not an endomorphism selected
by a quadratic root at the residue point. Put
\(b_\Delta=\Delta/p\in\mathbb Z_p^\times\).
The exact first-order relation from that ramified calculation is
\[
 H_p'(\lambda_a)\frac{\lambda_a^{\mathrm{CM}}-\lambda_a}{\epsilon}
  =c_a\,\frac{\sqrt{\Delta}/\epsilon}{b_\Delta}
       \quad\bmod\epsilon .
\]
Here any lift of the residue value over the unramified base
gives the same infinitesimal coefficient: differences are in
the ideal \((p)\subseteq(\epsilon^2)\).
The endomorphism square identity and \(H_p'\ne0\) are
essential. They do not determine the weight-two value.

The sum of the differential readouts is therefore
\[
  \mathcal J_p=
   \sum_{a\in\operatorname{Cl}(\mathcal O_\Delta)}\psi(a)c_a
   \frac{f_N(B_a,C_{N,a};\eta_a)}
        {2\lambda_a(\lambda_a-1)H_p'(\lambda_a)} .
\]
The reduced first coefficient of \(t([4]Q')/\epsilon\)
is exactly \(\mathcal J_p\) times the common nonzero scalar
\(4\bar u_p(\sqrt{\Delta}/\epsilon)/\bar b_\Delta\).
Here \([4]\bar Q'=O\) at the ramified mover because the
anti-involution of \(\mathbb Q_p(\sqrt{d'})/\mathbb Q_p\)
acts trivially on the residue field and sends \(Q'\) to
\(-Q'\); its residue before multiplying has order dividing
two. First-order coefficients add under the group law with
translation-invariant differentials, even for summands whose
residues are not \(O\). The common scalar's sign and field
are those of the one local orbit. This normalization tests
the same marked derivative previously identified with the
component-stripped additive residue. Fine Hodge choices
cancel: the scaling of \(c_a\) follows the scaling of the
Hasse differential at its zero, while the weight-two value
and its cotangent-square frame cancel each other.

At a ramified mover the class of its ideal \(\mathfrak p\)
has order two and is nonprincipal (it is one proper
member of the ramified prime ideal roster). The
degree-\(p\) CM isogeny gives the actual paired residue
label by relative Frobenius: a supersingular elliptic
curve has no separable degree-\(p\) isogeny, and transport
of the existing tame cyclic mark is étale. The
endomorphism at that paired label is the Frobenius
conjugate of the old one, by commuting with the same CM
isogeny, so the scalar inside the sum is \(s_a^p\) if
it was \(s_a\) at the first label, using conjugate gauges.
Consequently one may use the actual paired terms
\(\psi(a)(s_a+\psi(\mathfrak p)s_a^p)\) on the
\(\mathfrak p\)-orbits, where
\(\psi(\mathfrak p)=(h'/p)\) is the unramified
genus value (never a symbol with numerator \(d'\)).
This is a trace/anti-trace on the actual residue data,
not a nonvanishing result; the common \(\sqrt{\Delta}/\epsilon\)
factor has the compensating Frobenius sign.

## 3. What the normalized q-expansion certifies, and what it does not

At infinity \(a_1=1\) certifies that the reduction of
\(\omega(f_N)\) is a nonzero holomorphic differential.
The standard exact genus data are index
\(630374400\), 128 cusps, no order-2 elliptic points
(the 3-mark excludes them) and no order-3 elliptic points
(the 2-mark excludes them); these stabilizer checks also
hold in good characteristic \(p>3\). Thus the genus is
\(52531137\) and the divisor of the nonzero differential
has degree \(105062272\), independent of \(p\).
In particular at most that many distinct supersingular
marked labels have zero weight-two value. The complete
geometric supersingular label set has
\((p-1)\cdot630374400/12\) points: the Hasse section
has exactly this degree by Kodaira–Spencer and the logged
cusps, is simple in a fine Legendre chart, and is a unit
at the cusps. The upper fraction of bad ambient labels
is thus strictly below \(2/(p-1)\).
This is **not** a distribution assertion for the selected
CM reductions, which can repeat labels, or an exclusion
of cancellation among nonzero summands.

A supplied global algebraic differential can be verified
by its q-expansion to any order greater than \(2g-2\)
in the width-one parameter (the difference would have
too large a divisor of zeros). Hecke multiplicativity
and the actual counts on \(E^\flat\) supply its newform
coefficients. For example the exact point counts are
\(414744\) at the fixed mover \(415721\), and \(9805732\)
at the old order pilot \(9807649\); traces are respectively
\(978,1918\), both ordinary on the target. The latter
prime is **not** a support prime of the new same-scale
\(b\). Neither nonzero Fourier coefficient is a value
of \(f_N\) at the CM mark. A q-series around infinity,
as opposed to an algebraic model or appropriate finite
evaluation rule, is not a table of marked supersingular
weights.

There is a cheap normalized local sign canary, distinct
from the production modular form. On the independent
ramified \(p=7\), \(\epsilon^2=-7\) CM model
\(y^2=x^3+5x/16-\epsilon/32\), the three roots are
\(-\epsilon/4,(\epsilon+1)/8,(\epsilon-1)/8\).
They give \(\lambda=(-1+3\epsilon)/(1+3\epsilon)
\equiv-1+6\epsilon\bmod\epsilon^2\).
The literal Legendre scalar has \(H_7'(-1)=6\bmod7\),
so the jet is \(+1\), and the corresponding KS factor
on \(\partial_\epsilon\) is \(5\bmod7\).
An independent literal two-isogeny for the same model:
take the kernel root \((\epsilon+1)/8\), scale quotient
by \(s=(1+\epsilon)/2\) (its short coefficients are
\((5-15\epsilon)/32,(35-9\epsilon)/64\)).
Its trace is 1 and differential \(s\), so \([2]\gamma-1\)
has oriented differential \(\epsilon\) and degree 7.
Over \(\mathbb F_7[v]\), \(v^2=3\), on the residue
curve \(y^2=x^3-x\) take \(Q=(v,3+5v)\).
Then \(\gamma Q=(4+v,3+6v)\),
\([2]\gamma Q-Q=(-v,4+5v)=-F(Q)\), whereas
\(F(Q)=(-v,3+2v)\). The degree-seven zero-derivative
endomorphism is Frobenius followed by one of the four
automorphisms of this \(j=1728\) curve; the displayed
coordinates distinguish them and give \(-F\). Its
oriented coefficient \(c=-1\) thus agrees with the
positive Hasse jet for \(b_\Delta=-1\).
This is a distinct two-isogeny check of the same sign as
Joined's direct degree-seven quotient; it does not
substitute a low-level modular form for \(f_N\).

## 4. Optional finite sieve for *variable* movers; no compatibility assumed

Let the finite characteristic-zero zero divisor of
\(\omega(f_N)\) away from the cusps be marked and let
\(L_{\rm crit}\) be a finite Galois field containing its
point fields, the fields of a good representative
elliptic curve of each critical \(j\), and the full
\(\ell_0\)-torsion fields of these representatives
for an odd prime \(\ell_0\). Omit finitely many
bad primes of the divisor and the models, so
specialization of the zero divisor is the special
zero divisor (one may spread out the generic relative
Cartier zero scheme and take these exclusions).
If a large \(p\) splits completely in \(L_{\rm crit}\),
every critical point reduces with underlying elliptic
curve ordinary: at residue degree one this curve has
all its \(\ell_0\)-torsion rational and
\(p\equiv1\bmod\ell_0\), incompatible with the trace-zero
count \(p+1\) of a supersingular curve over \(\mathbb F_p\).
Hence this **sufficient** extra condition forces every
supersingular marked weight to be a unit. It does not
control the signed sum. One can take \(\ell_0=19\)
cyclotomically compatible with the two pilot residues
\(415721,9807649\equiv1\bmod19\) (whereas taking
\(\ell_0=3\) already conflicts with the first pilot).

There is no assertion that the added complete splitting is
compatible with the actual order and Gaussian selection.
Over the same Gaussian base, if \(L_0\) is the exact old
finite governor and \(\mathcal C\) its allowed Frobenius
classes, the finite intersection condition is precisely
that an allowed class restricts to identity on
\(L_0\cap L_{\rm crit}\) (using composita with the Gaussian
base). This condition is necessary and sufficient to
choose a compatible finite Frobenius class in the
compositum, not by itself to discharge the old independent
tails or future contact constraints; those must be
verified with the extension retained and its exclusions
included. No such intersection or adapted tail is computed.
It supplies no information about the already fixed
literal \(p_a=415721\), which cannot be reseived.
Even successful all-local unit certification leaves
weighted cancellation and the actual kept contact
class unresolved.

Replay: python3 -B check_jet_weights.py | cmp - EXACT-JET-WEIGHTS.json .

