# From the actual rational canonical differential to the same Abel period row

Paper identification, with specified strictly checked Lean inputs.
This is a local comparison on the original ordinary \(J\)-chart of the
selected compact modular curve \(X\). The target Abel map is into the
Jacobian \(J_X\) of this same curve. It is not the separate abelian
variety used elsewhere in the arithmetic argument.

## 1. Fix the rings and the literal ordinary evaluation map

Use the existing actual primitive polynomial \(p\) and the same rational
ordinary ring
\[
A=\mathbf Q[J,\,1/(J(J-1728))][x]/(p_{\mathbf Q}).
\]
Here \(p_{\mathbf Q}\) is the coefficient image of the original \(p\), not
a polynomial obtained by choosing a new root. Write \(j_X,x_X\in A\)
for the given coefficient \(J\) and the given monogenic root. In the
strictly checked compact output these are the ring
SelectedOriginalRationalOrdinaryRoot318.ordinaryRoot, the element
SelectedOriginalCompactClassicalDifferentials318.jInRoot, and the
literal AdjoinRoot.root. Its inclusion into the actual compact
normalization is the open immersion ordinaryEmbedding. In particular
there is no choice of branch through an algebraically independent
ordered pair in this comparison.

If \(\tau\) is an actual admissible period with
\(j(\tau)\notin\{0,1728\}\), let \(\epsilon_\tau:A\to\mathbf C\)
send \(j_X\) to the literal analytic \(j(\tau)\) and \(x_X\) to the
literal marked arithmetic \(x(\tau)\). The original period-root
evaluation theorem records these two coordinate values
(SelectedWholeOrdinaryPath318.rootEval_coordinates);
the complex-root field theorem records the literal root relation over
those evaluations (SelectedActualComplexWholeRootField318.returns_whole_root_set).
The coefficient map from the original localized \(J\)-ring to the
rational ordinary ring sends the old \(J\) to \(j_X\), and the rational
root map sends its original root to \(x_X\). Rational scalars have their
fixed embedding into \(\mathbf C\). It follows directly from the
universal properties of polynomial ring, localization and quotient
that \(\epsilon_\tau\) exists, is unique, and restricts to exactly
the originally checked evaluation; it is not a newly matched complex
point. Namely, the literal denominator is nonzero, and the rational
coefficient relation vanishes because the original relation already does.
Thus the ordinary period morphism in these coordinates is the map
\(\Pi:\tau\mapsto\epsilon_\tau\) to this very \((\operatorname{Spec}A)^{an}\).

On any sufficiently small complex disk \(D\) about \(\tau\) in the
admissible upper half-plane, the three evaluations of
\(j_X\), \(1/(j_X(j_X-1728))\), and \(x_X\) are holomorphic in the
literal period coordinate \(z\). The first and last are the
original analytic \(j(z),x(z)\); the middle is their genuine
rational coefficient denominator, which stays nonzero on \(D\).
These elements generate the rational algebra \(A\). Therefore
\[
E:A\longrightarrow\mathcal O(D),\qquad a\longmapsto
                  \bigl(z\longmapsto\epsilon_z(a)\bigr)
\]
is a well-defined rational algebra hom into holomorphic functions.
No choice of analytic continuation of an individual coefficient
has entered; evaluation of finite expressions in these three
generators gives the same function for every expression of the
same \(a\). This only requires holomorphicity of the literal
\(j\) and marked \(x\) near the selected ordinary periods; the
native continuous_periodCoordinates proof in the same strict
tree uses their existing analytic germs.

## 2. Differentiate the ring evaluation, not an independently attached form

Define the \(\epsilon_\tau\)-scalar \(A\)-module \(\mathbf C\) and the
rational derivation
\[
\delta_\tau(a)=\left.\frac{d}{dz}\epsilon_z(a)\right|_{z=\tau}.
\]
It is rational linear since all rational constants evaluate to fixed
complex constants; the complex analytic product rule gives precisely
\(\delta_\tau(ab)=\epsilon_\tau(a)\delta_\tau(b)+
\epsilon_\tau(b)\delta_\tau(a)\). Hence the universal Kähler property
induces one \(A\)-linear contraction
\(\kappa_\tau:\Omega_{A/\mathbf Q}^1\to\mathbf C_{\epsilon_\tau}\)
with \(\kappa_\tau(da)=\delta_\tau(a)\). This is the coefficient of
the analytic pullback along \(\Pi\), evaluated on \(d/dz\): equality
on \(da\) and on scalars follows by the definition of analytic
differentiation, and these identities characterize the map on all
Kähler differentials. This determines the analytic coefficient, rather
than comparing two independently named coefficients up to a constant.

For any global rational canonical differential \(w\) on the actual
compact model, let \(w_A\) be its restriction to this ordinary
open. The exact strictly checked frame \(F_A=\mathrm{ordinaryFrame}\)
sends \(d j_X\) to \(1\). Write \(r_w=F_A(w_A)\), the actual
rationalCoefficient of the same \(w\). Then
\[
w_A=r_w\,dj_X,\qquad
(\Pi^*w)_\tau(d/dz)
 =\kappa_\tau(w_A)
 =\epsilon_\tau(r_w)j'(\tau).                                      \tag{1}
\]
This formula uses the ordinary derivative of the literal \(j\), not
a derivative with respect to \(q\) or a choice of nonzero multiple
of \(dj_X\). It neither divides by \(j'(\tau)\) nor requires it
nonzero. The distinction matters if one transports a derivative to
a boundary chart. This statement is made here only where the ordinary
evaluation is defined.

By the checked original_canonical_from_both_charts theorem the same
\(r_w\), on either of the two exact rational normal charts \(i=0,1\),
equals
\[
F_A\!\left((\mathrm{ordinaryFromChart}_i)_*
                    \mathrm{chartRestriction}_i(w)\right).
\]
Thus (1) reads the exact period coefficient from either normal
chart using one \(dj_X\), with no second choice of tangent frame
or reciprocal-chart scalar. The chart maps are characterized on
the actual generic field by intoOrdinary_at_generic. The factor
\(j'(\tau)\) comes only from differentiating that actual ordinary
period evaluation.

## 3. The original ordered Hodge frame, including number-field scalars

For a number-field frame \(w_i\) rather than only rational \(w_i\),
the construction is unchanged at its given embedding
\(\sigma:K\hookrightarrow\mathbf C\). The base-change map
\[
K\otimes_{\mathbf Q}H^0(X,\Omega_{X/\mathbf Q}^1)
       \;\xrightarrow{\sim}\; H^0(X_K,\Omega_{X_K/K}^1)
\]
is the literal one. To see its exactness here, use a finite affine
cover of the separated curve: each pairwise intersection is affine,
global sections are the kernel of the two restriction maps on finite
products of affine sections, and tensoring with the field \(K\) is
flat and commutes with these finite products. Formation of Kähler
differentials on each affine commutes with this scalar extension
by its universal property. This proves the stated global map and
identifies restrictions to the ordinary chart, not just their
dimensions. The checked normalized étale frame also preserves
\(dj_X\) under its scalar extension (tensorFrame_normalized).

Consequently the lifted evaluation is exactly
\(\epsilon_{\sigma,\tau}(\lambda\otimes a)
=\sigma(\lambda)\epsilon_\tau(a)\); coefficients evaluate in the
same given embedding. Applying (1) linearly to the *original* ordered
frame gives the actual period coefficient of each \(w_i\), including
when the frame originates in the arithmetic Hodge lattice after
passing to its generic fiber. This does not assert an integral
basis or claim a uniqueness of arithmetic models.

Let \(\eta_i\) be the unique invariant coframe of the actual \(J_X\)
whose pullback under its own pointed \(a\) equals \(w_i\). The
[actual Abel pullback isomorphism](https://jmilne.org/math/xnotes/JVs.pdf#page=6)
and the independently signed same-J derivative/Haar proof identify
\(\kappa_{\sigma,\tau}(w_i)\) with the derivative of the actual
degree-one Abel logarithm in the exact \(\eta_i\)-coordinate. Hence,
at the original ordered period tuple \((\tau_j)\), its ordered sum
matrix is not simply postulated to agree with an algebraic frame:
\[
D(\log F)_{ij}
   =\epsilon_{\sigma,\tau_j}(r_{w_i})j'(\tau_j),\qquad
\det D(\log F)
   =\det\!\bigl(\epsilon_{\sigma,\tau_j}(r_{w_i})\bigr)_{ij}
         \prod_j j'(\tau_j).                                     \tag{2}
\]
The determinant identity is just column scaling, valid including
a singular column. It uses the same differential basis and
same \(z_i\)-coordinates on the actual \(J_X\) that specify the
target Haar measure. No \(2\pi i\) is lost: if one first writes
an analytic modular coefficient against \(dq_w/q_w\), changing
to the \(d\tau\) used here multiplies that coefficient by
\(2\pi i/w\), with the actual cusp width \(w\). Formula (1)
already uses the actual \(d\tau\) coordinate.

**Scope.** The comparison is on the exact original ordinary period
chart and both original algebraic canonical restrictions. It
supplies actual row equality even though the earlier native algebraic
chart and analytic measure theorems had disjoint types. It does not
build the compact modular analytic uniformization, the algebraic
Jacobian, the cusp disks or a native height theorem. The small
native SelectedActualRationalDifferentialPeriodDerivation318 packet
implements the universal period-evaluation derivation and normalized
frame identity, subject to supplying the literal rational evaluation
family and its generators in Lean. The proof above supplies that
specialization for the exact existing rational chart on paper.
