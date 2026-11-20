# Literal generalized carrier: explicit genus-one calculation and exact group/kernel boundary

Original 318/326, baseline **558a130e12a461d9b380b44510d457f0d3d8a29d**. This is a paper producer on the **same** two charts as **SelectedGeneralizedSmoothProperCarrier318**, not a replacement curve.

Let \(R\) be a commutative ring, \(J\in R\), \(d=J-1728\in R^\times\), and \(\epsilon=d^{-1}\). The generalized cubic is
\[
Y^2Z+XYZ=X^3-36\epsilon XZ^2-\epsilon Z^3 .
\]
Its discriminant \(J^2\epsilon^3\) is a unit when \(J\) is a unit. The two exact standard affines \(Z=1\) and \(Y=1\) cover the cubic: otherwise \([X:0:0]\) would satisfy \(X^3=0\) on the projective support. Write \(x=X/Z,y=Y/Z,t=X/Y,z=Z/Y\), and \(e=[0:1:0]\).

## Actual affine coordinate modules

Reorder the finite-chart variables to view \(y\) as coefficient variable and \(x\) as the root. The equations are literally
\[
A_Z=R[y][x]/(x^3-(y+36\epsilon)x-(y^2+\epsilon)),\qquad
A_Y=R[z][t]/(t^3-(z+36\epsilon z^2)t-(z+\epsilon z^3)).
\]
Both displayed polynomials are monic cubics. Thus the indicated powers \(1,x,x^2\) and \(1,t,t^2\) give the three-coefficient free expansions over their respective coefficient rings, irrespective of nilpotents or zero divisors in \(R\). For the zero ring all expressions and modules are zero. The same overlap is \(A_Y[z^{-1}]=A_Z[y^{-1}]\), compatibly with \(y=z^{-1}\) and \(x=t/z\); substitution into the finite equation multiplies the infinity equation by \(z^{-3}\). This is exactly the reciprocal overlap already pinned for the original literal carrier.

Identify \(A_Y[z^{-1}]\), as an \(R\)-module, with finite coefficient sequences on \(\{0,1,2\}\times\mathbf{Z}\), through the basis \(t^i z^n\). The infinity restriction \(A_Y\) occupies precisely \(n\ge0\); the finite restriction \(A_Z\) occupies precisely \(n\le-i\) in the \(i\)-th row because \(x^i y^j=t^i z^{-i-j}\), \(j\ge0\). Both restrictions are injective. Their intersection has exactly the basis vector \((i,n)=(0,0)\); their sum misses exactly \((i,n)=(2,-1)\).

## Cohomology and fibers

All repeated finite intersections of the ordered cover are affine. The alternating normalized two-open Čech complex therefore computes cohomology of \(\mathcal O\), by [Stacks 30.2.6](https://stacks.math.columbia.edu/tag/01XD) and the usual alternating Čech complex. Its only differential is \((a,b)\mapsto b|_{Y\cap Z}-a|_{Y\cap Z}\). Hence
\[
H^0(E,\mathcal O_E)=R,\qquad
H^1(E,\mathcal O_E)=R\cdot[t^2/z]=R\cdot[x^2/y],\qquad
H^i(E,\mathcal O_E)=0\quad (i>1).
\]
These are compatible with arbitrary \(R\to R'\): the coefficient support partitions, basis, two restriction formulas and scalar extensions are literal for the specialized same cubic. This does not need a generic coherent base-change theorem. The \(H^0\) calculation in a geometric fiber also forces connectedness (a nontrivial disconnection would give a nontrivial idempotent). The already supplied unit-discriminant gradient covers give a smooth proper relative curve of dimension one, so \(h^1=1\) gives genus one on every geometric fiber. No component is chosen.

## Precisely what this buys for the vertical different

Apply [Katz–Mazur §2.1, Theorem 2.1.2 (Abel)](https://math.bu.edu/people/jsweinst/AWS/Files/KatzMazurArithmeticModuli.pdf) to this proper smooth genus-one curve with this section: the unique group law is on this very carrier and has identity \(e\). Its multiplication \([M]\) is the same iterated point-law morphism, not merely a morphism on the same coarse parameter. [Katz–Mazur §2.3, Theorem 2.3.1](https://math.bu.edu/people/jsweinst/AWS/Files/KatzMazurArithmeticModuli.pdf#page=42) makes it finite locally free of rank \(M^2\) for every integer \(M\ge1\); no unit hypothesis on \(M\). The true kernel is the flat pullback of the effective Cartier zero section and finite locally free over \(R\). The existing actual identity-jet proof computes \([M]\) on its cotangent by \(M\), and group translation then supplies \(\Omega^1_{R[E[M]]/R}\cong R[E[M]]/(M)\). This is the precise same-coordinate input feeding the cyclic cotangent/trace-dual source, with no degree or Hodge normalization change.

## Exact Lean boundary

- **SelectedGeneralizedSmoothProperCarrier318**, source **44380bd9be95b436635ec0673f3de9cef80d50cf5c076a75462570c436a619b4**, builds the two-chart closed, smooth, proper carrier.
- **SelectedGeneralizedCechLaurentGap318** implements the finite-support intersection constants and the cokernel missing coefficient, with arbitrary \(R\); this leaf alone does not link those modules to global sections of the actual charts.
- **SelectedGeneralizedInfinityRegularZ318** expresses the actual infinity chart as the monic AdjoinRoot over \(R[z]\). The matching monic-in-\(x\) presentation of the actual finite chart over \(R[y]\), then porting the powers across the original reciprocal overlap, are separate native seams.
- Čech-to-sheaf cohomology, the Abel group-law theorem and Katz–Mazur full finite-flat theorem are paper imports, not new native declarations. The exact test-scheme **SelectedGeneralizedGeometricMulJet318** is source-only and consumes actual completed addition, not a field-only point operation or an assumed differential value.
