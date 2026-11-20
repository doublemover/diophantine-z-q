# The whole ordinary sign chart from the actual period map

Scope: the selected full signed level \(N=M(u,v)>4\) and the literal \(J\)
projection. This comparison does not import a compact complex curve,
an isogeny field, a Hodge lattice, or a Petersson norm.

## 1. One branch-free, same-coordinate map

Put \(W=\mathbb C\setminus\{0,1728\}\). The project short curve over W
is \(Y^2=X^3-3vX-2v\), \(v=J/(J-1728)\).
For \(\Lambda_\tau=\mathbb Z+\mathbb Z\tau\) use the uniformizing mark
\(z_N=1/N\), coordinates \(x_\tau=\wp_\tau(z_N)\),
\(y_\tau=\wp'_\tau(z_N)/2\), and short coefficients
\(A_\tau=-g_2(\Lambda_\tau)/4,B_\tau=-g_3(\Lambda_\tau)/4\).
Then \(y_\tau^2=x_\tau^3+A_\tau x_\tau+B_\tau\). The mark has exact
order N: \(k/N=m+n\tau\) forces \(n=0\) and \(N\mid k\).
Normalized \(J(\tau)\) is \(1728\cdot 4A_\tau^3/(4A_\tau^3+27B_\tau^2)\);
the literal curve has this same J by substitution. Over W all
four short coefficients are nonzero. Set
\(\alpha=(-3v)/A_\tau,\ \beta=(-2v)/B_\tau\).
Equality of J gives \(\alpha^3=\beta^2\), so for either square root s
of \(\beta/\alpha\) we have \(s^4=\alpha,s^6=\beta\). The resulting
pointed short-curve isomorphism \((x,y)\mapsto(s^2x,s^3y)\) gives the
same normalized x for both roots:
\[
X_N(\tau)=\frac{2 A_\tau}{3 B_\tau}\,\wp_\tau(1/N).
\]
No branch of a square root enters \(\Phi_N(\tau)=(J(\tau),X_N(\tau))\).

For continuity (indeed holomorphy), on compact \(C\subset\mathfrak H\)
one has \(|m+n\tau|\ge c\|(m,n)\|\) uniformly: take the positive
minimum over C times the real unit circle. For \(\lambda=m+n\tau\)
with \(|\lambda|\ge2|z_N|\), the paired Weierstrass summand is
bounded by \(10 |z_N|\,|\lambda|^{-3}\), by expanding the numerator
\(2z_N\lambda-z_N^2\) and using the reverse triangle inequality.
Away from finitely many (m,n), this estimate holds uniformly.
The remaining finitely many terms have no poles on \(\mathfrak H\),
as \(z_N\notin\Lambda_\tau\). The exponent 3 is summable on the
rank-two lattice; the exponents 4 and 6 for \(g_2,g_3\) are as well.
Normal convergence gives holomorphy in \(\tau\). The denominator
\(B_\tau\) does not vanish on \(\mathfrak H^\circ=J^{-1}(W)\).
The exact deleted set is the two full modular orbits of \(i,\rho\).
[Sutherland, MIT 18.786 Lecture 19 §19.1](https://math.mit.edu/classes/18.786/2024/LectureNotes19.pdf)
supplies the Weierstrass model, normalized J, and uniformization;
the normal-convergence check above is the needed parameter argument.

## 2. Image is the whole literal sign chart, over the same J

Let U be the actual sign chart of the exact-order N locus of this
literal curve, i.e. its quotient by \(P\mapsto-P\), not a component
or a new moduli scheme. Its complex points are exactly pairs
\((J,X)\) from the primitive points: nonzero points are affine,
equal x gives the same ordinate up to sign, and the finite
geometric quotient has precisely those orbits. The algebraic seam
is SelectedPrimitivePowerBasis318.actual_primitive_powers and
SelectedPrimitiveXCharacteristic318.characteristicEquiv_root
in j1-literal-powers-successor, with the actual kernel input of
ActualMulKernelFiniteEtale318.kernel_finite_etale on this base.
Thus the same monogenic chart U(C) is the zero set of \(P_N(J,X)\)
in \(W\times\mathbb C\) with its subspace topology. Its \(X\) is
the actual marked x, not an arbitrary algebra generator.

The scale and exact order in §1 show \(\Phi_N(\tau)\in U(\mathbb C)\).
Conversely, lift a point of \(U(\mathbb C)\) to the displayed short
curve with actual mark up to sign and uniformize the pointed curve.
An oriented period basis writes the mark as \((a+b\tau)/N\) for
\((a,b)\) primitive mod N. It can be made the first period divided
by N by determinant-one change of basis. Explicitly, complete the
primitive vector to determinant 1 modulo N using Bézout. Reduction
of \(\mathrm{SL}_2(\mathbb Z)\) surjects onto
\(\mathrm{SL}_2(\mathbb Z/N)\): over each prime-power local factor
a unimodular column has a unit entry, so row swaps, eliminations
and an elementary product for \(\operatorname{diag}(u,u^{-1})\)
generate; CRT gives elementary parameters supported in each
factor, and each transvection lifts integrally. Renormalize the
first oriented period to 1 to obtain \(\tau'\in\mathfrak H^\circ\).
The computed scale returns the original pair \((J,X)\), not merely
some point over the same J: it and the original analytic
identification differ by a pointed automorphism of the ordinary
short curve, necessarily ±1. Thus no point of the full chart is
omitted; no cardinality comparison is used.

For \(\gamma=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\),
multiplication by \(c\tau+d\) identifies \(\Lambda_{\gamma\tau}\)
with \(\Lambda_\tau\) and sends the source mark to \((c\tau+d)/N\).
Ordinary automorphisms being ±1, equality of the normalized
marks up to sign is equivalent to \(c\equiv0,d\equiv\pm1\bmod N\).
The determinant condition gives that same sign for a. The fibers
are exactly the actual \(\Gamma_1(N)\)-orbits because central
\(-I\) acts trivially on the domain. Both the analytic modular
projection to W (free effective ordinary quotient) and the
analytic literal algebraic projection to W (simple root of the
same polynomial) are local biholomorphisms. The established
over-W bijection is a local biholomorphism by using the same local
coordinate J on both covers. No compact complex comparison is
needed. [Snowden, Lecture 12, “Description of Y1(N)”](https://websites.umich.edu/~asnowden/teaching/2013/679/L12.html)
confirms the \(1/N\) mark and the modular subgroup convention.

## 3. Connectivity, full generic field, and what is still native work

The exact punctured half-plane is path connected: identify
\(\mathfrak H\) homeomorphically with \(\mathbb C\) by
\(x+iy\mapsto x+i\log y\), and remove the two countable orbits.
The continuous surjection makes the whole \(U(\mathbb C)\) path
connected. It also gives algebraic connectedness: a nonempty
algebraic clopen in this finite-type complex scheme has a complex
closed point, and gives an analytically clopen subset of U(C).

In the whole compactification over \(\mathbb P^1_\mathbb C\)
obtained by normalization in the full generic algebra, all
components meet U by construction in generic fields. For an
actual pure one-dimensional finite modular compactification with
this identified ordinary open, the same holds because a whole
one-dimensional component cannot lie in finite fibers over
0, 1728 or infinity. A separation would disconnect U. Regularity
makes distinct irreducible components disjoint, hence U and its
compactification are integral. In particular the full affine
generic algebra is one field; arbitrary coefficient extension
of arbitrary finite algebras does not give this result.

Exact native scope (source-only, no hosted verdict):
* SelectedActualOrdinaryConnected318 has the punctured genuine
  upper half-plane topology and its actual Gamma1 quotient.
* SelectedHolomorphicSignCoordinate318 has the exact scale and
  continuity algebra. For the geometric connectedness use, the
  weakest remaining native input is a continuous surjection of
  the punctured upper half-plane into the whole complex locus of
  the actual monogenic chart; §§1–2 prove that paper result
  without compact GAGA. A native producer needs the genuine
  lattice uniformization and normal-convergence statements plus
  the same primitive-kernel-to-sign-point comparison. The
  compact finite/normal object and its dense ordinary chart
  remain independent geometric constructions.
* Use of SelectedCanonicalCompactScalar318 and
  SelectedRationalCompactScalarLift318 then transports over
  precisely J with no chosen component. No compact complex
  Riemann-surface comparison, Jacobian identification,
  Hodge/Petersson Gram, or stable finite-trait model is claimed.
