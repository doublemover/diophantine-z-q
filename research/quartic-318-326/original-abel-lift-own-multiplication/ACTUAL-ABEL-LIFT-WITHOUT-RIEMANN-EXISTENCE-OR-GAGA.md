# The pointed Abel lift on the same \(J_X\) through its own multiplication

This is a classical proof for the actual smooth proper \(X=X_1(M)_\mathbb C\) and its actual Jacobian \(J_X\). The point of the reduction is not to reconstruct an algebraic Jacobian from an analytic torus. It only identifies the period cover through a finite subgroup of \(J_X\) itself. The argument uses neither Riemann existence for general covers nor GAGA for morphisms or coherent sheaves.

## 1. The comparison is a factor of the given Jacobian's [n]

Write \(V=\operatorname{Lie}(J_X^{an})\), \(e:V\to J_X(\mathbb C)\) for its actual exponential, \(\Lambda_J=\ker(e)\), and \(\Lambda_X\) for the integrals of the actual pullback coframe along pointed closed paths on \(X\). The chosen coframe and the pointed algebraic Abel morphism \(j_X:X\to J_X\) are unchanged. Lifting \(j_X\)-paths shows \(\Lambda_X\subseteq\Lambda_J\); the harmonic primitive argument in the same-J companion shows finite index. Choose any \(n>0\) with \(n\Lambda_J\subseteq\Lambda_X\). Define
\[
T=e((1/n)\Lambda_X)\subseteq J_X[n](\mathbb C).
\]
This is exactly the subgroup to quotient by, not the kernel of some independently selected isogeny. By the standard finite subgroup quotient for an abelian variety in characteristic zero (Milne, *Abelian Varieties*, section on isogenies: [course notes](https://www.jmilne.org/math/CourseNotes/AV.pdf)), form the actual algebraic \(Y=J_X/T\). Multiplication by \(n\) on \(J_X\) factors as the quotient map followed by the finite étale homomorphism \(\beta:Y\to J_X\). The analytified quotient has the quotient topology: the finite surjective algebraic quotient is closed on complex points by compactness and Hausdorffness. Its fibers are exactly the \(T\)-cosets.

The explicit continuous group map
\[
\alpha:V/\Lambda_X\longrightarrow Y(\mathbb C),\quad
[v]\longmapsto [e(v/n)]
\]
is an isomorphism of topological groups. It is surjective by surjectivity of \(e\) and of scalar division. If \(e(v/n)\in T\), choose \(w\in\Lambda_X\) with \(e(v/n)=e(w/n)\). Then \((v-w)/n\in\Lambda_J\), so \(v-w\in\Lambda_X\) and \(v\in\Lambda_X\). The quotient map is open because both quotient group maps, \(e\), and division are open. In these exact coordinates
\[
\beta\alpha([v])=[n]e(v/n)=e(v),
\]
the original period comparison. This also fixes the pointed local branch and, since both sides are covers of the same complex manifold, gives the usual analytic comparison locally by the inverse sheets. No choice of periods, coframe, curve, or Jacobian is changed.

## 2. Analytic connectedness here via a monic generator, not GAGA

The only algebraic-to-analytic connectedness needed below has an elementary finite-chart proof. Let \(C\) be an integral smooth proper complex curve with a finite nonconstant map \(J:C\to\mathbf P^1_{\mathbb C}\). This will be used for \(X\) and the algebraic connected components of one finite étale pullback of \(X\), always with the same composed \(J\).

Let \(F=\mathbb C(C)\), a finite separable field over \(\mathbb C(J)\). A primitive generator can be multiplied by a nonzero element of \(\mathbb C[J]\) so that it satisfies a monic minimal polynomial \(p(J,T)\in\mathbb C[J][T]\): if the first minimal equation has coefficients \(a_i(J)\), multiplying the generator by a common denominator \(d(J)\) replaces \(a_i\) by \(d^{\deg_T(p)-i}a_i\). This still generates the same \(F\), and the monic equation is separable over \(\mathbb C(J)\).

On the finite base outside the finite zero set of its nonzero discriminant, the normalized curve has exactly the simple roots of \(p\). Indeed the monogenic model on that open is finite étale over a normal base, hence normal, and has the same fraction field \(F\); the finite dominant map from the normal curve is the normalization there. Denote this connected open set of complex \(J\)-values by \(U\). The simple roots are local holomorphic functions on \(U\) by the ordinary one-variable implicit function theorem.

Suppose \(C(\mathbb C)\) had a nontrivial clopen subset \(D\). The finitely many excluded points of \(C(\mathbb C)\) have empty interior in the smooth complex curve, so both \(D\) and its complement meet the simple-root preimage of \(U\). Over \(t\in U\), take the products of \(T-u\) over roots labelled by \(D\) and by its complement. Since \(D\) is clopen, any local analytic root branch over a small connected disk stays in its own part. The two monic products therefore descend to single-valued holomorphic coefficient functions on \(U\). Their \(T\)-degrees are locally constant, hence globally constant on \(U\); both are positive.

The root bound for a monic equation gives
\[
|u|\ \le\ 1+\max_i |a_i(t)|\ \le\ C_0(1+|t|)^d
\]
for constants \(C_0,d\), independently of the branch. For the first inequality, if \(|u|>1+\max_i|a_i(t)|\), the geometric sum bounds the total of the lower powers strictly below \(|u|^{\deg_T p}\). Each product coefficient is thus bounded in a punctured neighborhood of every deleted finite value and has polynomial growth at infinity. Riemann's removable-singularity theorem extends it to an entire function. Cauchy's estimates at the origin force every Taylor coefficient above the growth exponent to vanish, so the two products have coefficients in \(\mathbb C[J]\). Their product equals the original \(p\) on \(U\) and therefore in \(\mathbb C[J][T]\), contradicting irreducibility over \(\mathbb C(J)\). Thus \(C(\mathbb C)\) is connected.

The proof uses only one monic generator in the actual field of each algebraic component. It does not change the original \(J=1\) polynomial or choose a substitute field for the compact height argument. The monic generator serves only to test connectedness of the finite pullback below.

## 3. The exact algebraic section comes from a degree-one component

The usual pointed period lift sends \(X(\mathbb C)\) to \(V/\Lambda_X\); a point reached by a path from the fixed base point is sent to the endpoint of the lift of \(j_X\) in \(V\), modulo the same \(\Lambda_X\). Composing with \(\alpha\) gives a continuous lift of the given \(j_X^{an}\) to \(Y(\mathbb C)\) through the algebraic finite étale \(\beta\), sending the fixed base point to zero.

Form the literal pullback \(Z=X\times_{J_X}Y\) with \(X\to J_X\) equal to \(j_X\). Its projection \(q\) to \(X\) is finite étale; \(Z\) is smooth proper. Its algebraic connected components are finitely many disjoint integral curves: smoothness gives local domains, so irreducible components cannot meet, and Noetherianity gives finiteness. Every nonempty such component surjects onto \(X\) since its image is both open and closed. They inherit the finite nonconstant map to \(\mathbf P^1\) by composition with the original \(J\)-map, so §2 shows that each analytified component is connected. Conversely they partition \(Z(\mathbb C)\) by clopen subsets. Thus the algebraic components give exactly the analytic connected components.

The pointed continuous lift is a section of \(Z(\mathbb C)\to X(\mathbb C)\). In any sufficiently small connected evenly covered open, its image is exactly one sheet there, so its full image is clopen. The image is connected since \(X(\mathbb C)\) is connected, and hence is precisely the component through the selected point. Consequently the corresponding algebraic component is finite étale of degree one over \(X\), as seen by counting any one complex fiber, and is an isomorphism (equivalently, finite birational to a normal target). Its inverse gives the pointed **algebraic** lift through the original \(q\). This construction does not algebraize arbitrary analytic maps or analytic covers.

## 4. Actual pointed Albanese uniqueness finishes

Pointed algebraic Albanese universality for the actual \(j_X\) (Milne, *Jacobian Varieties*, Proposition 6.1: [chapter](https://jmilne.org/math/xnotes/JVs.pdf)) gives a homomorphism \(s:J_X\to Y\) through which the pointed algebraic lift factors. Uniqueness of the factorization of \(j_X\) through itself gives \(\beta s=\operatorname{id}_{J_X}\). On the given \(Y(\mathbb C)\simeq V/\Lambda_X\), the residual map \(1-s\beta\) takes values in \(\ker\beta\), killed by \(n\), and \(V/\Lambda_X\) is \(n\)-divisible. The residual map is zero. It follows that \(\beta\) is an isomorphism and the **same** two lattices coincide, \(\Lambda_X=\Lambda_J\). The coframe comparison is the originally normalized exponential on the originally chosen periods, not an arbitrary identification of complex tori.

## Exact proof boundary

The companion native sources give the explicit factor through the actual group's [n], the homeomorphism over it, and the algebraic split-kernel argument. A native project application still needs the real scheme \(Y=J_X/T\), the complex-point realization of the actual smooth \(J_X\) and finite étale pullback, and the actual pointed algebraic Albanese universal property. The monic-generator proof isolates a smaller native analysis task instead of assuming all of GAGA or Riemann existence: show that coefficients of a clopen-selected factor on a holomorphic simple-root open extend to polynomials by removable singularities and a growth estimate. Neither the finite-sheet proof nor the companion group theorem produces a Hodge metric or identifies \(J_X\) with the unrelated abelian surface \(A\).
