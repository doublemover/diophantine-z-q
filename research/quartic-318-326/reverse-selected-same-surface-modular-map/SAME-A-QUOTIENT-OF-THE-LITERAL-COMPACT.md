# The selected non-CM surface is a quotient of the literal modular Jacobian

**Paper producer, not a Lean declaration.** Start with the single primitive
counterexample pair selected from the specified literal 318/326 witness, its
actual odd-contact support \(S\), and \(M=2^{28}3^6S^2\). Use the original
fine-fibre PEL construction for its \(D=210\) point \(s=u/v\) (not a
different rational point on a geometrically isomorphic model). Let \(A/F\)
be that actual polarized maximal-order QM surface, non-CM in this branch.
Let \(X_M^{\rm lit}\) be the whole original projective normalization used
by the height proof. The classical ordinary-moduli comparison underlying
the canonical compact result is over \(\mathbb Q\), on the actual signed
primitive point chart over the original \(j\)-line.

The conclusion, using the named classical results below, is that there
exists a primitive weight-two \(g\) of level \(n\mid M\) with nebentypus
\(\varepsilon\), and a surjection
\[
 f:\operatorname{Jac}(X_M^{\rm lit})_E\longrightarrow A_E,\qquad
 E/F\text{ cyclic},\qquad
 [E:\mathbb Q]\le 1152\,|\operatorname{im}\varepsilon|\le 1152\,\varphi(n).
\]
Inflate \(\varepsilon\) by the cyclotomic character modulo \(n\). More
precisely, if \(F_\varepsilon=F\overline{\mathbb Q}^{\ker\varepsilon}\),
then \(F_\varepsilon\subseteq E\), \(F_\varepsilon\subseteq F(\zeta_n)\), and
\([E:F_\varepsilon]\le2\). The induced quotient
\(B'=\operatorname{Jac}(X_M^{\rm lit})_E/(\ker f)^0\) and isogeny \(B'\to A_E\)
are over that same \(E\). No bound on the degree of this last induced
isogeny is asserted. The improvement over the existing \(2304n\) receipt
is that the residual determinant sign is provably absent, yielding the
quadratic-over-nebentypus construction; no additional endomorphism,
normality of \(F/\mathbb Q\), symplectic QM comparison, or new modularity
assumption is needed.

## 1. Modular form and divisibility, on this same selected \(A\)

The nonbranch fine fibre of the fixed \(D=210\) model has at most
\(16\cdot36=576\) geometric points; a residue field \(F\) of one point
defines the polarized \(A\) and its full specified maximal-order action.
It is the point used by the directional height comparison. Non-CM
implies geometric simplicity and the exact endomorphism algebra: if
simple, its division endomorphism algebra acts on the four-dimensional
rational homology and hence has dimension dividing four, so it equals
the specified quaternion algebra. A product of two nonisogenous
elliptic curves has commutative endomorphism algebra; a square of a
non-CM elliptic curve has the split four-dimensional matrix algebra.
Neither can contain the division algebra. A square of a CM elliptic
curve is CM, which is the other branch. The tame model
off the literal support gives unramified local marked lifts with good
reduction. We use this actual application of the PEL model, not an
arbitrary numerical \([F:\mathbb Q]\) estimate. Every place is potentially
good: after semistable extension the torus, if nonzero, would carry a
unital action of the division algebra \(B_{210}\) on its rational character
space of dimension \(1\) or \(2\). A nonzero module over that division
algebra has dimension over \(\mathbb Q\) divisible by four. Extension of
endomorphisms to the semistable model makes this argument on the same
\(A\); it does not require the special fibre to remain simple.

Since the image of \(s\) downstairs is rational, the conjugate marked
points are related by the actual Atkin–Lehner action.
[Guitart–Molina, Corollary 2 and the opening of §3](https://arxiv.org/pdf/0906.2559#page=4)
give compatible conjugate isogenies, hence compatibility with the entire
geometric endomorphism algebra \(B_{210}\), since the order spans it.
With center \(\mathbb Q\), Schur index two and dimension two, \(A\) is a
building block. Apply [Guitart, Theorem 3.3 converse](https://arxiv.org/pdf/1102.0863#page=10)
and [Guitart–Quer, Proposition 2.3](https://doi.org/10.4153/CJM-2012-040-2)
(Ribet/Serre modularity over \(\mathbb Q\)) to obtain one primitive \(f_0\)
with \(A_{f_0,\overline{\mathbb Q}}\) isogenous to a power of this \(A\).

At the auxiliary primes 3 and 7 the same \(f_0\)'s multiplicity-space
projective action is the one from the quaternionic-compatible isogenies.
Indeed on a common normal finite extension the comparison is isotypic
with absolutely irreducible multiplicity space by Faltings; comparing
conjugations of this normal subgroup makes the ratio scalar globally.
The finite projective wild \(p\)-subgroup, for \(p\) different from the
auxiliary prime, injects into the division
order reduction quotient of sizes \(8\) and \(16\) respectively, modulo
the pro-auxiliary group. Use auxiliary 3 except at the residue prime 3,
where use 7. Thus projective wild inertia is zero at odd primes and
has size at most \(8\) at 2. Off \(S\) actual good unramified marked
lifts kill all projective inertia, not merely its wild part.

The established single global unit-character correction applies to this
same \(f_0\): cancel the entire scalar inertia off \(S\); cancel scalar
wild inertia by the inverse square root of the \(p\)-primary determinant
at odd primes of \(S\); and at 2 choose the inverse determinant
square root on \(1+4\mathbb Z_2\), extended trivially on \(-1\).
The finite unit CRT produces one global character \(\chi\), realizing
these inertia characters (uniformizer freedom is irrelevant).
Take \(g\) to be the primitive form of \(f_0\otimes\chi\). At 2 the
normalized determinant on inertia is of order at most 2;
the linear wild scalar kernel then has order at most 4, so the full
linear wild order is at most 32. In a faithful finite congruence
quotient of this finite inertia the ramification different bound gives
last upper break at most \(2v_2(e)\le10\). Swan is at most 20, plus the
tame term at most two. At odd primes of \(S\) we have tame exponent at
most two and off \(S\) exponent zero. Monodromy is zero by potential
good reduction and finite twisting. [Carayol's Theorem A](https://archive.numdam.org/articles/10.24033/asens.1512/)
and the local newvector conductor theorem thus give
\(a_2(g)\le22,\ a_p(g)\le 2\ (p\mid S,\ p\ne2),\
a_p(g)=0\ (p\nmid S)\), hence genuine divisibility \(n\mid M\).
These local-normalization applications are the exact older checked
same-form donors pinned below; we do not use a conjectural rank theorem.
The field of a geometric power isogeny is not being bounded and need not
equal any height-evaluation field. Also \(A_g\) is not identified with
\(A_{f_0}\) over \(\mathbb Q\).

## 2. Exact determinant from potential absolute irreducibility

Work at \(\ell=11\), a split prime of \(B_{210}\), in the covariant Tate
convention. Matrix units for the **defined-over-\(F\)** QM action give
\[
 V_\ell(A)=W\oplus W,\qquad\dim W=2
\]
over \(G_F\). For **every** finite extension \(K/F\) all geometric rational
endomorphisms are still exactly \(B_{210}\) and defined over \(K\).
[Faltings](https://doi.org/10.1007/BF01388432) gives semisimplicity
and \(\operatorname{End}_{G_K}V_\ell(A)=M_2(\mathbb Q_\ell)\) from the
QM action. Therefore \(\operatorname{End}_{G_K}W=\mathbb Q_\ell\).
Commutants commute with scalar extension here: the matrix commutation
equations are generated by a finite-dimensional span. In characteristic zero
semisimplicity is preserved by scalar extension, so \(W\) remains
absolutely irreducible over **each** such \(K\).

The polarization on \(V_\ell(A)\) gives a pairing to
\(\mathbb Q_\ell(1)\); at least one of its four \(W\times W\) blocks is
nonzero. That block yields a perfect \(G_F\)-equivariant
\(b:W\times W\to\mathbb Q_\ell(1)\) by irreducibility. Transposition
acts on the one-dimensional space of such forms as \(+1\) or \(-1\)
because it squares to identity. If \(b\) were symmetric, over
\(\overline{\mathbb Q}_\ell\) its isotropic lines in dimension two would
be two distinct points, permuted by the actual similitude action.
The kernel of this permutation is open: the two-point line set is
discrete in its finite coefficient extension, and the action is continuous.
Its corresponding finite extension of \(F\) would leave an invariant
line, contradicting the preceding potential absolute irreducibility.
Consequently \(b\) is alternating; in dimension two its similitude
multiplier is exactly the determinant. Thus
\[
                    \det W=\chi_{\rm cyc},
\]
not merely \((\det W)^2=\chi_{\rm cyc}^2\). This argument uses the actual
polarization but does not choose a quaternionic Rosati matrix, fix a
sign by convention, or infer irreducibility just from a small commutant.

## 3. Descent and the actual normalized-curve map

Over a finite Galois extension of \(F\) which defines the geometric
power isogeny and kills \(\chi\), the chosen \(\ell\)-adic constituent
\(\rho_g\) of the actual \(A_g\) is \(W\). Fix an identification there.
As before, normality of the subgroup and the scalar commutant show on
all of \(G_F\) that \(\rho_g=\lambda W\) for a continuous character
\(\lambda\). Its definition is independent of scaling the comparison;
even a different finite comparison field gives the same character for
these representations, by intersecting their open subgroups and
applying irreducibility and Schur there. No normality of \(F\) over
\(\mathbb Q\) is assumed. The covariant determinant of the genuine
newform constituent is \(\det\rho_g=\varepsilon\chi_{\rm cyc}\).
Combining this with §2 gives
\[
     \lambda^2=\varepsilon|_{G_F},\qquad
     G_E=\ker\lambda,\qquad [E:F]\le2|\operatorname{im}\varepsilon|.
\]
The same formula proves the claimed quadratic relative extension.
The field of roots of the coefficients of \(g\) is not an extra
number-field extension in this estimate. Over \(E\), projection to the
chosen \(A_g\) constituent followed by inclusion of \(W\) into \(V_\ell(A)\)
is a nonzero equivariant map over \(\overline{\mathbb Q}_\ell\).
Applying a \(\mathbb Q_\ell\)-linear functional nonzero on one matrix
entry gives an equivariant map downstairs, since the two full Tate
actions have base-field matrix entries. Faltings Hom over \(E\) gives
an actual nonzero morphism \(\phi:A_{g,E}\to A_E\).

The whole literal compact is the finite normalization of \(\mathbb P^1_j\)
in the full signed primitive ordinary field. Its classical over-\(\mathbb Q\)
identification \(\kappa_M:X_M^{\rm lit}\simeq X_1(M)\) is the unique
extension of the actual ordinary-moduli identification by normality,
as in the same-curve canonical simplification. On that same dense
moduli open apply \((C,[\pm P])\mapsto(C,[\pm(M/n)P])\); the target has
exact order \(n\), the assignment is rational, and it commutes with
the **one simultaneous sign**. By the properness of the classical target
and the DVR local rings of the source the map extends uniquely across
all its omitted points. Equivalently, the same \(j\)-field inclusion
extends by finite normalization. The source can be kept as
\(X_M^{\rm lit}\) throughout. The resulting map
\(\pi_n:X_M^{\rm lit}\to X_1(n)\) over \(\mathbb Q\) is finite and
nonconstant since it respects the nonconstant \(j\). This uses no shape
or degree of its cusp divisor and no independent comparison at level
\(n\). For the target classical point-level modular Jacobian the genuine
newform quotient \(q_g:J_1(n)\twoheadrightarrow A_g\) is rational
(Eichler–Shimura/newform decomposition and dual rational isogeny if
needed). On the source's actual Jacobian, the pushforward/norm of
\(\pi_n\) is onto, since norm after pullback is multiplication by the
positive degree on \(J_1(n)\), as follows on point divisors.
The actual promised map is
\[
              f=\phi\circ q_{g,E}\circ(\pi_n)_{*,E}.
\]
The image of \(\phi\) is a nonzero abelian subvariety of the geometrically
simple \(A_E\), hence all of \(A_E\); all the other arrows are epi.
The connected identity component \(K=(\ker f)^0\) and the quotient
\(B'\) are defined over \(E\) in characteristic zero. Use **this**
\(B'\) when applying Gaudron–Rémond, rather than putting a degree bound
on the induced isogeny \(B'\to A_E\).

## 4. What the same-curve simplification actually removes

The rational ordinary identification and uniqueness of normalization
remove a separate compact-model comparison assumption for the modular
map above. In particular no arbitrary complex isomorphism may be used
to wind up with a \(\mathbb Q\)-twist and a hidden extension of \(E\).
They also transport the same stable Jacobian through an honest
\(\mathbb Q\)-isomorphism. The degree-free separation argument at \(j=1\)
gives \(g_X=\dim H^0(X_M^{\rm lit},\Omega)\le d\le M^2\) without a canonical
divisor degree formula. The produced surjection implies \(g_X\ge2\).
Thus the strict numerical consumer needs no independent genus
upper/lower calculation or adjunction-based divisor count for
nonsingular-minor selection. It still needs the actual all-place
Hodge bound for **this** Jacobian, the true directional height for
the same \(A\), and the Rémond/Bost/GR applications. In particular,
generic comparison proves no semistable or wild trace statement.
Nor does it supply the PEL/modularity step in §1. The selected CM branch
and the final literal source integrality are separate.

**Exact predecessor pins** (SHA-256): fine fibre and tame support
FIBER-PRODUCER.md 86f5a70d…; building block a37a6dba…; same-form global
projective comparison 098f0d3d…; twist 85604541…; older small-field
dc4441d6…; over-\(\mathbb Q\) compact + \(dj\) 113bc488…; scalar lift
04303810…; degree-free separator d46da580…; exact strict consumer
ccf78f07…. They are source/application proofs, not native premises
mysteriously discharged by this note. No Lean build is claimed.
