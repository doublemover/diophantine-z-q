# The actual two-class cover can be made to lift to Selmer four, without factoring the fixed coefficients

Use the exact two-class family from e649acb1 and the exact quotient and
local tables from 92707c5c. Keep the original fixed positive retuned
labels, the sixteen incidence balls, the slots and roots
s=−32/(407c₁²)<0<t=1/(2399c₂²), and the two distinct pilots
pₐ=415721, pᵦ=9807649. Write δ=t−s, a=pₐqₐ, b=pᵦqᵦ, D=ab.
Here qₐ,qᵦ are the separately produced compatible primes, B the
original saturation integer, L the preceding finite index CRT modulus,
and S' the sixteen retained primes and qₐ. First fix an allowed qₐ;
the choice below concerns qᵦ only.

**Claim.** One can choose qᵦ satisfying the actual two-class
orientation, old and new residue contacts, common even index CRT, and
real acceptance of the original construction, so that the marked class
α=(D,b,a) of the locally soluble genus-one curve
w²−s=aU², w²−t=bV² lies in the image of
\(\operatorname{Sel}_4(E_D)\to\operatorname{Sel}_2(E_D)\) on the
actual Jacobian \(E_D:y²=x(x-Ds)(x-Dt)\). This is orthogonality against
the **whole** 2-Selmer group. In particular there is an everywhere
locally soluble 4-cover lifting this 2-cover, and [C] is in
\(2\Sha(E_D)[4]\). No actual numeric qᵦ or lift is computed. This
does not give a rational point on either cover, rank, a full
description of the 2-Selmer group, a local incidence refinement on
the 4-cover, or all original factors. Paper only.

## 1. A fixed normalized Selmer space and its marked vector

The local images at any moving prime consist of the four distinct
torsion-valuation rows; see §1 of 92707c5c. For each Selmer class
subtract the unique rational torsion Kummer class that removes its
valuation vector at qᵦ. The resulting cocycle is locally trivial
at qᵦ (not just unramified). Normalization identifies the quotient
by the two torsion Kummer directions with a subspace of
\(H^1(\mathbf Q,E_1[2])=\operatorname{Hom}(G_{\mathbf Q},E_1[2])\).
The latter identification is literal: the full rational 2-torsion
has the same labeled roots across all twists. The squareclass
coordinates of a cocycle F are the three characters
\(e_2(F,T_i)\), in root order 0,s,t; nonzero torsion values
\(T_0,T_s,T_t\) have character-bit triples 011,101,110.

The normalized subspace V is the same for every admissible qᵦ in
the two-class proof. Indeed all normalized tuples have no qᵦ
factor. At primes of B and infinity the exact conditions are those
of \(E_1\), since D is a local square. At the other three moving
primes all mutual Legendre symbols are fixed + by §1 of 92707c5c.
At qᵦ itself the tuple restricts trivially exactly when all its
coordinates have square sign there. These signs depend only on
the fixed units of a tuple: their supported B parts by
\(q_b\equiv p_b\bmod8B\) and reciprocity, and their supported
\(p_a,q_a,p_b\) parts by the checked + symbols. At any other
prime the support is unramified and the local image is the whole
unit image. Consequently V is a single finite linear space, not
a family of bases depending on qᵦ. We use its existence, not its
unknown dimension or a factorization of B.

The qᵦ-normalized marked cocycle is
\[
 F_*=(t,a\delta,a t\delta),
\]
because the t-root torsion triple is \((Dt,D\delta,t\delta)\).
It is nonzero (its first class is 2399). Write \(G=\mathbf Q(i)\)
and \(\varepsilon=\chi_{-1}\) in additive notation. At \(p_a\) and
at 2399 choose inertia elements \(\iota_a,\iota_0\in G_G\) with
\[
 F_*(\iota_a)=T_0,\qquad F_*(\iota_0)=T_t .
\]
At the first prime t and δ are units and a has depth one, so a
nontrivial a-inertia gives 011. At 2399 the exact local ratio row
makes both t and δ have odd valuation and a is a unit, so a
nontrivial t-inertia gives 110. The base extension \(G/\mathbf Q\)
is unramified at both primes, so those inertia choices belong
to \(G_G\).

## 2. Two central inertias on the fixed order-selection field

Let \(F_{\rm ord}/G\) be the old finite compositum for selecting
qᵦ in e649acb1: fixed Gaussian ray modulo 8B and the stripped
index modulus, the finite order Kummer/torsion layers, and
the ray modulo the retained primes in S'. Its inertia image is
central at \(p_a\), since this prime was stripped from the index
modulus and only the abelian S' ray is ramified there.

There is a second central inertia, at 2399. The exact XVI
CRT modulus has \(L\bmod2399=221\). The first producer fixes the
Gaussian generator of qₐ congruent to \(475+436 i\) modulo 2399
because 2399 divides B. Its two group sizes are the unordered
norms \(N(\pi_a\pm1)\); modulo 2399 these are 1645 and 2144.
Both point orders for qₐ are therefore prime to 2399. The
updated index modulus \(L_a\) is the lcm of L, those two
orders and \(q_a^4\), so 2399 still does not divide it.
Consequently the order Kummer/torsion layers for qᵦ, whose
prime levels divide the stripped \(L_a\), are unramified at
2399: the two literal curves have good reduction there
(their possible bad primes are 2,7), and the division fibers
are finite étale at 2399. Only the abelian Gaussian ray
can be ramified there, so this inertia image is central in
\(F_{\rm ord}/G\) as well. Central means central over G; we do
not assert it after adjoining rational complex conjugation.

## 3. Governing cochains for this fixed marked row

Use [Smith, *Governing fields and statistics for 4-Selmer groups and
8-class groups*, Lemma 3.1 and Theorem 3.2 with proof](https://arxiv.org/pdf/1607.07860).
Here the base elliptic curve for that theorem is \(A=E_{a p_b}\);
the twisting parameters are two admissible primes qᵦ and qᵦ′. Use
the set of places consisting of infinity, primes of B, and
\(p_a,q_a,p_b\). It includes 2 and all bad places of A;
the class group of Q is trivial. The ratio \(q_b/q'_b\) is a
square at each place of this set, by the identical fixed ray
phase and the equal inter-prime signs; normalized \(F_*,F\) are
in both Selmer groups for every \(F\in V\).

For clarity the cochain description of the theorem is as follows.
Let \(\langle\, ,\,\rangle\) be the Weil form in F₂. For each \(F\)
choose the normalized additive 1-cochain \(\Gamma_F\) with
\[
 d\Gamma_F(g,h)=\langle F_*(g),F(h)\rangle .
\]
The proof of Smith 3.2 shows these can be taken with values in F₂
and factored through a finite Galois extension of Q unramified
outside the stated places: the global cup is trivial by local
Kummer isotropy and Brauer reciprocity/injectivity; Kummer Hilbert
90 gives the F₂-valued primitive; and a quadratic character
removes additional ramification. The resulting central extension
is at most quadratic over the elementary abelian field where
both cocycles trivialize. This is the cochain in Smith's (3.3),
not the degree-16 generic construction of his (3.4).
In particular \(\Gamma_F\) is additive on the common kernel of
the two characters. On commutators, its exact value is
\[
 \Gamma_F([g,h]) =
 \langle F_*(g),F(h)\rangle+\langle F_*(h),F(g)\rangle. \tag{1}
\]
Indeed the central extension of the abelian quotient defined by
the cup has this commutator, or evaluate the coboundary on
\(gh\) and \(hg\); inverse signs coincide in F₂.

Take a common finite Galois compositum H of these fields and of all
the normalized cocycle fields (a basis of V suffices). After base
change to G and composition with \(F_{\rm ord}\), let Z be the
subgroup generated by all commutators \([\iota_a,g],[\iota_0,g]\)
for \(g\in G_G\). All its images in \(F_{\rm ord}\) are trivial
by §2. All images in the cocycle fields are trivial because those
fields are abelian. Moreover this is a central subgroup in the
whole compositum over G: the projection to \(F_{\rm ord}\) is
trivial, and on every governing field it belongs to a central
quadratic kernel. By (1) its action yields a subspace of the
linear functionals on V, all vanishing at \(F_*\).
For example choose primitives on a basis and extend linearly;
changing any primitive by a quadratic character leaves these
commutator evaluations unchanged.

## 4. Exact annihilator: one odd-depth fixed collision suffices

Suppose \(F\in V\) is annihilated by all these commutator evaluations.
Since \(F_*(\iota_a)\), \(F_*(\iota_0)\) are independent, (1) shows
that on \(G_G\) there is a unique linear map \(J:E[2]\to E[2]\)
with \(F=JF_*\): for each value \(u=F_*(g)\) the two lines of (1)
uniquely specify \(F(g)\) by the perfect Weil form. Setting \(g\)
equal to the two chosen inertias in (1) says J is self-adjoint.
On \(G_{\mathbf Q}\), we can only conclude
\[
 F=JF_*+\varepsilon v
\]
for some \(v\in E[2]\); the correction must not be dropped.

The following exact local lines determine this correction.

* Over R, \(F_*=0\) since its three squareclasses are positive;
  the local Kummer image has positive s-coordinate, so
  \(v\in\langle T_s\rangle\).
* At 3 the fixed local image has square s-coordinate. Here
  \(F_*=\varepsilon T_s\) locally: its first entry t has
  nonsquare unit class 2399 and hence class −1, and its second
  entry aδ has trivial class (δ is a square unit after square
  scaling, since \(v_3(T)=2\) and \(-S\) is a square unit).
  Thus J preserves \(\langle T_s\rangle\).
* At 2 the fixed local image has square t-coordinate. Here
  \(F_*=\varepsilon T_t\) locally: the two classes t,δ are
  both −1, and a is a square by the old ray. Thus
  \(JT_t+v\in\langle T_t\rangle\).

In the symplectic ordered basis \(T_s,T_t\), the self-adjoint
maps with the second property have matrix
\(\left(\begin{smallmatrix}u&w\\0&u\end{smallmatrix}\right)\).
The last forces \(v=wT_s\). Therefore either \(F=uF_*\) or
\(F+uF_*=(-a\delta,1,-a\delta)\) in squareclass coordinates:
the coefficient of \(T_t\) in \(F_*\) is the character of aδ,
and \(\varepsilon\) contributes the minus sign. The latter tuple
is not in V. In fact for the literal reduced c₁/c₂=m/n,
\[
 P=407m^2+32\cdot2399 n^2\equiv7\bmod8,\qquad
 (P,2\cdot11\cdot37\cdot2399)=1.
\]
The congruence uses the exact dyadic unit ratio, so both m,n
are odd. Coprimality follows from the exact unit rows at
11,37,2399 and their displayed coefficients. Thus there
exists an odd prime outside these four with \(v_p(P)\) odd.
The p belongs to B, because \(t-s\) has that odd valuation
after undoing the square scaling. It is not a moving prime.
The exact table has the s,t roots colliding at p and 0 separate,
so the first coordinate of any local Kummer class has even
valuation, **whether split or nonsplit**. But the first
coordinate of the proposed variant, \(-a\delta\), has odd
valuation there. This gives a factor-free contradiction
without locating this prime.

Thus the annihilator of Z is exactly \(\langle F_*\rangle\).
Finite-dimensional linear duality now says its image is all
\((V/\langle F_*\rangle)^\vee\). This establishes controllability
of a single marked row; it does not give freedom to impose an
arbitrary alternating matrix on two freely varying Selmer rows.

## 5. Choose the actual prime, preserve the analytic sieve, and conclude

Fix first an admissible reference prime \(q_b^*\) from the old
two-class construction. At a Gaussian prime over \(q_b^*\), take
a Frobenius lift \(g^*\) to \(HGF_{\rm ord}/G\) projecting to the
prescribed order and ray class (choose the place with the
original order-arm labeling). Its normalized cocycle projection
is trivial. The functional \(F\mapsto\langle F_*,F\rangle_
{E_{a p_b q_b^*},{\rm CT}}\) is zero at \(F_*\) by alternation.
Choose \(z\in Z\) realizing this functional in F₂ by §4.
Prescribe the Frobenius class of \(z g^*\) instead. This joint
class is nonempty and keeps the original F_ord restriction.

For two admissible primes the difference of the marked
pairings is exactly the sum of the two Frobenius bits of
\(\Gamma_F\) by Smith 3.2, or directly his (3.3). Indeed they
are outside the stated bad set and split in the field of the
two normalized cocycles; choose one prime of norm \(q_b\)
and one of norm \(q_b^*\) in that field, so the Artin comparison
of their quotient is the sum in F₂. The chosen representatives
may be taken to be \(zg^*,g^*\) by choosing the place over each
Gaussian prime. Since z fixes the class fields, evaluation
of \(\Gamma_F\) changes by its value on z. Accordingly the
new pairing functional is zero. This formula also makes the
normalization by rational torsion harmless, since rational
Kummer classes are in the pairing radical.

The positive Chebotarev density for this *fixed* class
goes through the original coprimality sieve. To check the
extra field seam, all new governing fields are unramified
outside the exact set of §3, whose finite rational support
is already included in the moduli for \(F_{\rm ord}\).
Thus every extra small-prime Gaussian ray used in the old
finite cutoff is linearly disjoint from the augmented fixed
field and preceding extra rays, by the same abelian
unramified-intersection and class-number-one argument.
The finite main-product density remains bounded below by
its new constant times the old positive convergent product.
The medium tail still needs only the fixed-field-independent
[Gaussian ray Brun–Titchmarsh bound, Theorem 3](https://arxiv.org/pdf/2210.11051);
the large tail is still the same Gaussian coordinate lattice
bound. Both are unchanged with the new positive constant:
choose the finite cutoff after this constant and then take
the asymptotic. Therefore an actual \(q_b\) satisfies the
prescribed mark and the same true odd group-gcd condition.
The original order caps, CRT, local depth/Hensel and real
density argument supply the identical kind of common h and
all retained local cells for this prime.

Finally the radical of the alternating Cassels–Tate pairing on
the actual 2-Selmer group is the image of Selmer four under [2];
see [Fisher, *On binary quartics and the Cassels–Tate pairing*,
Introduction](https://arxiv.org/pdf/2208.14977). We killed the
pairing against all normalized classes and rational torsion, so
the same marked α is in that image. This is not a proof that
α is a rational Kummer image or that its actual Sha class
vanishes. No assumption of finiteness of Sha is used.
