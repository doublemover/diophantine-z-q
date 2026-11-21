# An actual nonzero paired ramified CM term on the selected fixed-mover family

This is a nonzero **individual paired contribution** to
the exact moving differential sum, not a nonzero sum.
It keeps the lower semistable curve, chosen even auxiliary,
the exact same-scale selected Jacobian and both marked CM
orientation and contact data. No numerical selected
\(D\), value of \(f_N\) at a named label, rational point,
rank result, or local cell saturation is produced.

## 1. Fixed prime and unbounded actual family

Use \(N=205042530\), \(r=976393\), \(h'=-2207\), and the
actual fixed contact prime \(p=p_a=415721\) throughout.
Write
\[
 D=p_aq_aq_1q_2,\qquad d'=rD,\qquad \Delta=h'd' .
\]
For the selected family, \(q_a,q_1,q_2\) are the original
successively selected distinct Gaussian-norm primes of
the same-scale packet 70410179. In particular the
set of retained conditions is not relaxed: fix the
first two actual choices \(q_a,q_1\), and use the
last Frobenius class there with Cassels triple
\((0,0,1)\). The additional inertia-square adjustments
in its §3 only change the fixed finite governor.
Its same-scale proof explicitly reuses the two
positive-density tails of the first complete contact
class, section 4 of 336708e6:
the finite-ray density has positive lower bound
\(\delta\prod_{\ell\equiv1(4),\,\ell\ge5}
(1-4/(\ell-1)^2)>0\) independent of the cutoff;
the intermediate Gaussian ray Brun–Titchmarsh
tail is bounded by a fixed reciprocal-square
tail times \(X/\log X\), and the large-coordinate
tail is \(o(X/\log X)\). The base governor is fixed
once \(q_a,q_1\) and the three adjusted signs are
fixed; its finite bad primes are already those
of the frozen order/ray cut (the cochains are
ramified only on its fixed support). The original
closure uses this *positive* density after both
tails, not a finite search. Hence one can increase
the numerical lower bound on the last \(q_2\)
arbitrarily without changing \(a\), \(q_1\), the
prescribed signs, the old balls, or the exact CRT
completion afterwards. Thus the actual selected
fundamental discriminants \(\Delta\) are unbounded
while the mover \(p_a\) is fixed.

They are negative, odd, squarefree and fundamental,
with \(v_p(\Delta)=1\). Their level-prime behaviour is
split at \(2,3,5,7\), ramified simply at \(11,37,2399\),
as in the exact lower genus packet 3927abd5. In
particular \(\Delta\equiv1\bmod8\), accounting for the
dyadic split slot. At the ramified mover the unramified
genus value is
\(\psi(\mathfrak p)=(h'/p)=+1\), by Euler's criterion
on the actual \(h'\) (the argument below would also
apply with sign \(-1\)).

## 2. Primitive local representations in one actual marked order

Fix a supersingular marked point \(s=(B,C_N)\)
of \(X_0(N)\) at \(p\) such that the reduction of the
actual scaled newform differential at \(s\) is nonzero.
Such a point exists by the already checked divisor
bound 124f1017: the differential is nonzero since
its first q-coefficient is one, has at most 105062272
zeros, and the supersingular marked locus here has
21838270464000 points. We may also avoid \(j=0,1728\):
even each of their *bare* sets of possible marks
has at most 630374400 entries. No actual value of
the newform is assumed or computed at a named model.
Work over \(k=\mathbb F_{p^2}\), using \(B\) and its
mark over \(k\); square Frobenius on \(B\) is scalar,
so all its geometric endomorphisms are defined there.
If desired use the fine Legendre frame of 124f1017
over \(k\) to fix the invariant differential.

Use the actual definite quaternion Eichler order
\(R=\operatorname{End}(B,C_N)\) of level \(N\) in
the algebra ramified at \(p,\infty\), and the fixed
integral positive ternary lattice
\[
             L=(\mathbb Z+2R)\cap B_{\rm quat}^{\,0},
                      \qquad Q(v)=\operatorname{Nrd}(v).
\]
Here the superscript \(0\) means reduced trace zero.
Every admissible \(n=|\Delta|\) is locally primitively
represented in this very lattice:

* For every \(\ell\ne p\), act on the rank-two
  \(\mathbb Z_\ell\)-module \(\mathcal O_{K,\ell}\)
  by multiplication. This embeds it into the
  maximal split order. At \(\ell\mid N\) the
  local order is a stabilizer of a line modulo
  \(\ell\). In the split case choose an eigenline
  in \(\mathbb F_\ell\times\mathbb F_\ell\);
  in the ramified case choose the unique invariant
  nilpotent-ideal line in
  \(\mathbb F_\ell[t]/(t^2)\).
  Conjugate the frame to the prescribed local line.
  At **2**, split means
  \(\mathcal O_{K,2}=\mathbb Z_2\times\mathbb Z_2\);
  use the same coordinate line argument. It applies
  to the integer \((1+\sqrt\Delta)/2\) itself, not
  to an attempted division of a mod-2 matrix.
* At \(p\), \(K_p\) is a **ramified quadratic
  field**, which embeds in the quaternion division
  algebra: the local Brauer invariant becomes
  zero over a degree-two extension. Its ring of
  integers is contained in the unique maximal
  order there by the valuation description.
  The trace-zero uniformizer \(\sqrt\Delta\)
  lies in the maximal ideal \(\mathfrak P\)
  but not \(\mathfrak P^2=pR_p\).
* In these local embeddings the trace-zero vector
  \(\sqrt\Delta=2\cdot(1+\sqrt\Delta)/2-1\) is
  in \(L_\ell\) and has norm \(n\).
  It is primitive because otherwise division by
  an \(\ell\)-scalar in \(L_\ell\) would give
  \(\ell^2\mid n\), contrary to squarefreeness.
  The archimedean representation is automatic.
  Exact local solutions give positive local
  densities (the gradient of a nondegenerate
  form at a nonzero local vector is nonzero
  over the local field, even if divisible by
  the residue prime).

Conversely if \(v\in L\) represents \(n\), then
\(v^2=\Delta\). Write \(v=a+2b\) with \(a\in\mathbb Z\),
\(b\in R\). Since \(n\) is odd, \(a\) is odd; hence
\((1+v)/2\in R\). This embeds the **maximal**
\(\mathcal O_K\) and is automatically optimal:
there is no larger integral quadratic order containing
it. Its mark is the actual stable cyclic subgroup of
\(B\), not a \(j\)-only condition.

## 3. Prescribe a phase so even the actual Frobenius pair is nonzero

Use the fixed characteristic-zero root
\(+\sqrt\Delta\) in the oriented lift, and the Hodge
frame at the literal point \(s\). For a ramified
local embedding put \(v=\iota(\sqrt\Delta)\).
Its first nonzero formal term on \(B\) has degree \(p\)
and coefficient \(c(v)\in k^\times\); the same
comparison is used in 124f1017. It is unchanged
on \(v+\mathfrak P^2\), since this ideal gives
formal endomorphisms of height at least two.
For a local automorphism \(u\in R_p^\times\) with
Hodge tangent \(d\in k^\times\),
\[
                c(uvu^{-1})=c(v)d^{\,1-p}.
\]
This follows by composing the actual formal series:
the outer first derivative contributes \(d\), the
inner one \(d^{-p}\). The tangent reduction
\(R_p^\times\to k^\times\) is surjective from
the maximal division order; its kernel is
\(1+\mathfrak P\). Thus conjugation runs through
the **entire** norm fibre \(c(v)\mu_{p+1}\), while
preserving the trace, norm, and integrality of the
embedding.

Let \(F_s\in k^\times\) be the fixed actual
nonzero scalar multiplying \(c(v)\) in the known
Legendre formula for \(\mathcal J_p\) at \(s\),
removing the common scalar from all terms.
For the two classes paired by the ramified
ideal \(\mathfrak p\), the exact local contribution
before multiplying by the genus sign of the first
class is
\[
                 F_s c+\psi(\mathfrak p)(F_s c)^p .
\]
Its zero condition is one \(\mathbb F_p\)-linear
line in \(k\). Any such line contains at most
two elements of a fixed nonzero norm fibre
because the norm on it is a fixed nonzero
constant times the square of its scalar
coordinate. Since \(p+1>2\), choose a local
ramified embedding with nonzero pair contribution.

The chosen local coefficient is a congruence
on \(v\bmod pL_p\): for odd \(p\) the lattice
\(L_p\) is the full trace-zero part of \(R_p\),
and its intersection with \(pR_p\) is exactly
\(pL_p\). Given the chosen local vector, choose
an integral representative \(v_0\in L\) of that
coset. The congruence \(v\in v_0+pL\) retains
primitive local representability everywhere;
outside \(p\) the coset does not restrict it.

To globalize this congruence, apply
[Duke–Schulze-Pillot, Theorem 3 and Lemma 5](https://www.math.ucla.edu/~wdduke/preprints/lattice2.pdf)
to the shifted lattice with \(Q_1=p^2Q\) and
\(h=v_0/p\) in an integral \(L\)-basis.
Then \(Q_1(x+h)=Q(v_0+px)\).
Their possible restrictions on the square
factor of \(n\) are automatic since \(n\)
is squarefree; at the anisotropic mover the
valuation is always one. Lemma 5 and its
following explanation retain primitive
spinor-genus representation for all locally
primitive values outside finitely many
exceptional squareclasses. There are only
finitely many cosets \(v_0\bmod pL\);
take the finite union of their exceptional
classes and the maximum of their qualitative
thresholds, omitting cosets not used.
Each fixed exceptional squareclass contains
at most one squarefree \(n\).
Thus all sufficiently large selected \(n\)
have a **global** representative in the
chosen good-phase coset. The threshold is
not asserted effective.

## 4. The ramified lift and both original signs

The optimal embedding just constructed into
the actual marked order lifts with the required
ramified CM type. At \(p\) the supersingular
connected \(p\)-divisible group is a height-one
formal \(\mathcal O_{K_p}\)-module under this
embedding. Use the canonical lift with its
specified Lie map
[Gross, *Canonical and quasi-canonical liftings*,
Proposition 2.1 and its Serre–Tate discussion](https://archive.mpim-bonn.mpg.de/id/eprint/3578/1/preprint_1985_30.pdf#page=73).
Algebraize as an elliptic curve with the
endomorphism action by Serre–Tate; the
prime-to-\(p\) level subgroup lifts uniquely
by étaleness. The genuine characteristic-zero
CM order is maximal, so the elliptic curve
and its level quotient both have conductor
one. Its invariant and level structures
are those of an algebraic Hilbert class
CM point by ordinary characteristic-zero CM.
This uses the **ramified** local lift; it
does not invoke the inert-only wording of
Cornut–Jetchev Corollary 4.1. The general
adelic reduction theorem also permits
ramified \(p\), and their sections 4.7–4.9
identify the same good supersingular
reduction independently of that final
inert specialization.

The local \(\sqrt\Delta\) acts as the chosen
signed element on Lie in the canonical
lift. If it is described with the conjugate
CM type, replace the identifying embedding
consistently, not a separate per-summand
sign: changing both associated root
conventions changes a common sign but not
the proved nonzero pair. At each split
level prime the lifted stable line gives
one of the two orientations. Atkin–Lehner
at the subset of split primes where it differs
restores the actual level ideal \(\mathfrak N\).
It commutes with the ramified \(\mathfrak p\)
class action and multiplies the *differential*
by its same common sign \(w_S\in\{\pm1\}\).
It therefore preserves nonvanishing of the
entire pair. The genus character of
\(\mathfrak p\) is unchanged. This reaches
the selected class orbit, not an arbitrarily
oriented substitute. The three ramified
level classes still contribute the exact
factor 8 in the signed orbit sum, which is
a unit at \(p\). They are independent of
\(\mathfrak p\); the only relation of
ramified ideal classes is the product over
all ramified primes, not this proper subset.

**Conclusion.** For all sufficiently large
members of the same actual selected family
with \(p_a\) fixed, the exact reduced weighted
differential has at least one nonzero
contribution already after accounting for the
ramified \(p_a\)-pair and the three ramified
level classes. This is a genuine partial
anchor, not a numerical value of any
summand. Other selected classes can
cancel it modulo \(p_a\). No sparse dual
identity isolating the full sum from this
anchor is asserted; no point, complete
jet, rank or local-cell claim follows.

