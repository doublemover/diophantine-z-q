# The marked 4-cover can be chosen to admit the third factor everywhere locally

**Scope.** Preserve the exact three-factor family 48ae5e44 and its
original fixed index/scales, sixteen old contacts, seventeenth pilot,
and compatible new supports. In selecting the second new prime we refine
the whole marked-row argument 45899b89 to obtain a **pointed** Selmer-four
lift of the same raw class \(\alpha=(D,b,a)\). It is locally the zero
4-Kummer class at every prime of the fixed saturation integer \(B\)
except 2,3,47. These three exceptions require no pointing for the third
factor. Consequently the pullback of the genus-five cover to the
selected actual 4-cover is a smooth, everywhere locally soluble curve
of genus **17**. This is an existence theorem with standard arithmetic
duality, not numerical new primes, a rational point, full detector support,
or a Lean result. At the six moving support primes the assertion uses
unoriented \(w^2\) balls; it does not guarantee all prescribed old w-sign
representatives simultaneously on the 4-cover.

## 1. The exact local lift condition and its Poitou--Tate dual

Keep first \(q_a\) as in 48ae5e44, and write \(q\) for a variable
admissible \(q_b\), \(b=p_bq,\ D=ab,\ A_q=E_D\). Put
\[
 \mathcal P=\{p:p\mid B,\ p\notin\{2,3,47\}\}.
\]
This is a finite exact set, not an enumerated factorization. In the
raw \(\operatorname{Sel}_2(A_q)\) we have \(\alpha|_p=0\) at these
places, since \(a,b\) are both local squares. Normalize by the labeled
\(t\)-root torsion point \(T\) as in 45899b89, so the fixed normalized
class \(F_*=\alpha+\kappa_2(T)=(t,a\delta,at\delta)\) is trivial at q.
At a prime of \(\mathcal P\) prescribe the particular lift
\(\beta_p=\kappa_4(T)\) of \(F_*|_p=\kappa_2(T)\).
If a global Sel₄ lift obeys these local prescriptions, adding the rational
\(\kappa_4(T)\) recovers a lift of raw \(\alpha\) with local class zero:
\(\kappa_4\) is a homomorphism and \(2T=0\).
Elsewhere use the ordinary local 4-Kummer lifts.

Here are the exact local subgroups controlling this assertion. For
the coefficient sequence
\[
 0\longrightarrow A_q[2]\xrightarrow{j} A_q[4]
       \xrightarrow{[2]} A_q[2]\longrightarrow0
\]
write \(L_v\) for ordinary 2-Kummer in \(H^1(\mathbf Q_v,A_q[2])\).
Its annihilator under the local Weil-cup pairing equals \(L_v\)
by local Tate duality. At \(p\in\mathcal P\), to match a prescribed
local 4-class the allowed difference before applying \(j\) is
\[
 U_p=\ker\!\bigl(H^1(\mathbf Q_p,A_q[2])
                   \xrightarrow{j} H^1(\mathbf Q_p,A_q[4])\bigr)
     =\kappa_2(A_q(\mathbf Q_p)[2]).
\]
The equality is the connecting map for the displayed exact
coefficient sequence; it is the same Kummer boundary restricted
to 2-torsion. In particular **the dual local condition at such p
is \(U_p^\perp\), not all \(H^1\)**. This distinction permits the
cochain comparison below even when \(F_*|_p\) is nonzero. At all ordinary
places the preimage by \(j\) of the 4-Kummer subgroup is \(L_v\):
use the natural maps to \(H^1(\mathbf Q_v,A_q)\), whose kernels are
the respective Kummer subgroups. Thus define \(\mathcal V^+\)
to be the space of global dual classes with restrictions in
\(U_p^\perp\) at \(\mathcal P\) and \(L_v\) elsewhere.

A global cohomological lift \(\beta\in H^1(\mathbf Q,A_q[4])\)
of \(F_*\) exists before imposing the local prescriptions. Indeed
its boundary in \(H^2(\mathbf Q,A_q[2])\) restricts to zero everywhere
by the ordinary local lifts, and \(A_q[2]\simeq\mu_2^2\) so the
localization map on \(H^2\) is injective by Kummer Hilbert 90 and
Brauer--Hasse--Noether. Choose at ordinary places some local
Kummer lift \(\beta_v\), and at \(\mathcal P\) the prescribed one.
Let \(z_v\) lift \(\beta|_v-\beta_v\) through \(j\). Then
\[
 f_q(F)=\sum_v \operatorname{inv}_v(z_v\cup_{e_2} F_v)
 \qquad(F\in\mathcal V^+)                                            \tag{P}
\]
is well-defined: choices of local preimages differ by \(\ker j\),
contained in \(L_v\) at ordinary v and equal to \(U_v\) at exceptional
v; changes of ordinary Kummer lifts similarly change \(z_v\) by
\(L_v\); and changes of global lift are global \(j\)-images, killed
in the sum by reciprocity. The tuple lives in the restricted product
of the local \(H^1(A_q[2])\) groups. Only finitely many local terms
can contribute, by unramifiedness of the global lift outside a finite
set and the ordinary unramified Kummer lifts at good odd places.

Apply [Milne, *Arithmetic Duality Theorems*, I.4.10(b)](https://jmilne.org/math/Books/adt.html)
to the finite module \(A_q[2]\) with the Weil self-duality. In the
restricted product of the local \(H^1\) the image of global \(H^1\)
is the annihilator of the dual global image. Quotienting by the
product of \(L_v\) and \(U_p\) gives the corresponding exact
obstruction: this product is open (at almost all places it is the
unramified subgroup), so its sum with the global image is open and
closed. Taking the annihilator and back shows that the tuple
\((z_v)\) equals a single global class modulo these local subgroups
if and only if (P) vanishes on all of \(\mathcal V^+\). Correct
\(\beta\) by that global \(j\)-image to obtain exactly the pointed
Sel₄ lift. No claim about finiteness of the elliptic Sha is used.

The functional restricts to the ordinary marked Cassels pairing
on ordinary \(\operatorname{Sel}_2\): all selected \(\beta_v\) are
ordinary Kummer lifts, and a global cocycle lift makes the usual
global third-degree primitive zero. Hence it vanishes on rational
torsion Kummer and on \(F_*\) by alternation. Only the additional
dual directions in \(\mathcal V^+\) could add an obstruction.

## 2. The relaxed duals are fixed and the same cochain variation works

Normalize every dual class by the unique rational torsion
Kummer class removing its valuation vector at q (usual Kummer
there, with the four exact torsion parity rows). Normalized
classes restrict trivially at q, and form a single finite
space \(V^+\) independent of the admissible q. The proof is the
same finite support argument as in 45899b89: there is no q-coordinate;
the local images at old moving primes and q itself are read from the
exact equal clone signs; at the fixed primes of B, both the ordinary
Kummer conditions and the new \(U_p^\perp\) are transported through
the same local square scaling. Since the rational 2-torsion Kummer
subgroup is contained in its annihilator, subtracting rational
torsion stays in the full dual space. At all other primes the
good unramified image is unchanged. Ordinary rational torsion
Kummer accounts for all removed directions, already killed by (P).

For any fixed \(F\in V^+\) the cup \(F_*\cup_{e_2} F\) is locally
trivial: at usual places both classes are Kummer, and at \(p\in
\mathcal P\), \(F_*|_p=\kappa_2(T)\in U_p\) and \(F|_p\in U_p^\perp\).
Hence it has a global additive F₂-valued primitive \(\Gamma_F\),
by the same Brauer--Hasse and Kummer Hilbert 90 argument as in the
proof of [Smith, Theorem 3.2](https://arxiv.org/pdf/1607.07860).
The global primitive can be chosen through a central extension
at most quadratic over the cocycle class fields, with ramification
only at the primes of B and \(p_a,q_a,p_b\) (and infinity).
Indeed the initial primitive is a character on its common cocycle
kernel, so has exactly the same quadratic central construction.
Remove unwanted odd unramified-base prime supports by a rational
quadratic twist, exactly as in that proof. The two cocycles are
themselves unramified outside the specified fixed set. Their
commutator formula is unchanged.

Here one uses the **proof**, not the unmodified theorem statement
applied incorrectly to relaxed duals. For clarity, let q,q' be
two admissible primes and let \(\phi:A_q\to A_{q'}\) be the
usual isomorphism over the quadratic extension for \(d=q/q'\).
A global 4-cocycle lift \(\beta\) for q transports to a cochain
\(\phi\beta\) with differential \(\chi_d\cup F_*\), as in Smith
(3.1). A global primitive for its cup with F is
\(\chi_d\cup \Gamma_F\) (sign immaterial in additive two-torsion).
Thus (P) for q' can equivalently be computed by the usual corrected
local cocycles using these cochains: replacing \(\phi\beta\) by
a genuine global lift changes the discrepancy by the restrictions
of a global 2-cocycle, with total invariant zero. At every place
in the fixed set q/q' is square. One may choose the local lift for
q' to be the transport of the chosen lift for q, **including**
the prescribed \(\kappa_4(T)\), since the labeled roots are fixed
by the isomorphism. The two correction terms there cancel.
At another prime other than q,q', choose unramified local lifts;
the classes and governing field are unramified, so local
invariants of unramified cocycles vanish. At q and q' the two
normalized cocycles restrict trivially, and only the correction
\(\chi_d\cup\Gamma_F\) can contribute, through its unramified
quadratic character paired with odd valuation of d. This is
precisely the Artin comparison of Smith (3.3):
\[
 f_q(F)-f_{q'}(F)=\Gamma_F(\operatorname{Frob}_{q})
                  +\Gamma_F(\operatorname{Frob}_{q'})
                  \quad\text{in F}_2.
\]
The formula has no extra pointed correction depending on the new
prime. Its hypotheses at the exceptional places were checked by
exactly choosing \(U_p^\perp\), and at the other places are the
usual ones. Both governing Frobenius representatives are in the
kernels of the two involved cocycles.

## 3. The same two central inertias still control the entire enlarged row

Use the exact proof of 45899b89 on \(V^+\). The old order selector
with the seventeenth pilot has the same two central inertias
at \(p_a,2399\) over the Gaussian field, as proved in 48ae5e44.
Their values on \(F_*\) remain \(T_0,T_t\).
All new cochain fields are the finite central extensions in §2,
and the allowed commutators project trivially to the same original
order field. The previous annihilator argument used just:
the real positive middle coordinate; square middle coordinate at
3; square third coordinate at 2; and even valuation of the first
coordinate at a prime of odd depth in the fixed t,s collision.
The first three conditions are unrelaxed. For the fourth, use the
**explicit** prime 47, also unrelaxed. The exact computation of
ea83f1d1 gives
\[
 \eta\equiv1596\bmod47^2,\qquad
 407\eta^2+32\cdot2399\equiv1739=47\cdot37\bmod47^2,\quad
 (-814/47)=+ .
\]
Hence \(\delta\) has odd valuation at this prime and the roots
s,t collide with 0 separate in the square-scaled model. By the
exact local table the first coordinate has even valuation.
The extra possible function \((-a\delta,1,-a\delta)\) from the
Gaussian \(\chi_{-1}\) correction is therefore not in \(V^+\).
So the annihilator is still just the marked line.

Choose an old admissible reference q and compute its abstract
functional (P) on \(V^+\). It vanishes on the marked line as
shown in §1, so choose a product of central commutators giving that
whole row. Attach it to the reference Frobenius. This changes no
order or old ray phase. The new governing ramification is contained
in the same old modulus support, so the original finite ray
disjointness and the two analytic gcd tails go through with the
new fixed positive primary density. Thus an actual admissible q
annihilates all of (P) and has the desired pointed lift.
All pair supports, index clauses and exact older local cells
remain, including the new pilot p_c from the seventeen-row proof.
Choose q_c afterwards exactly as in 48ae5e44; this does not vary
the chosen marked curve or the lift.

## 4. The genus-17 pullback is everywhere locally soluble

Use the genuine 4-cover of raw \(\alpha\) from §1. At every
\(p\in\mathcal P\) its local 4-Kummer class is zero, so its local
identification as a 4-cover provides a point over the identity
of \(E_D\). This maps to a point at infinity on \(C_2\), and
\(C_3\) contains a local point above it since c is a local
square. One can also choose a nearby affine point, since
the \(C_4\to C_2\) morphism is étale and locally open and \(w\)
then has a pole. This explicitly handles, rather than ignores,
the previously forbidden phase at 5.

At 2 every local phase was already covered in 534279af.
At 47 the split s,t collision has odd depth, and \(-1\) is a
nonsquare. The separate torsion \(T_0\) gives a nonzero unit
row because its adjacent differences have class \(-s\)
in a square-scaled model; one of the colliding torsion rows
has nonzero valuation row. Together they exhaust the ordinary
local quotient of size four. Thus translation by deck torsion
allows the deep-denominator region in each phase.

At 3 the pair 0,T₀ in the integral square-scaled coordinates of
534279af is split of depth two. The t-root or zero-root torsion
contributes the nonsquare unit having first class 2399, so
one additional odd-parity local phase suffices modulo deck.
Use \(x=3\) in that integral model: both adjacent factors have
depth one and equal unit classes, and the separate factor is a
square unit. Here \(\eta\equiv6\bmod9\) and \(c_2\) is a 3-unit
(the actual product U has unit real part in the inert ring).
With \(C,S_0,T_0\) from the duplication formula in 534279af,
\((S_0,T_0/9,C/9,u)\equiv(2,2,1,2)\bmod3\).
Substitution gives \(w^2\equiv0\bmod3\); hence \(w^2-u\) is a
square unit. This supplies the missing odd phase, and applying
deck translations preserves \(w^2\). The even phases were
available near a point over infinity. Thus no 3-adic pointing
is needed.

At all six moving support primes, the real place, and all
remaining odd good primes, use §1 of 534279af: at the four old
moving primes deck torsion covers all local phases; at the
two third support primes the two sign orbits together do so.
Good primes allow the smooth genus-17 bound and Hensel.
This proves the all-place assertion for the **same** pointed
4-cover and third factor. The degree-two pullback has 32 simple
branch points over the genus-one curve and is geometrically
integral, hence genus 17. There is still no global rational
point or approximation theorem for rational points on these
covers proved here.
