# Independent cold review: the chosen primary scalar is positive residual Frobenius

**PASS** on the exact paper and finite controls, 21 November 2026. Author
paper `b1a2a78fd67550b14a46961ec236e5536eea6f28ce439f47c64757dac05d0d05`,
author checksum list
`b79108f8e2c23fa60c6a33c35020ae12c8e1c6e6ec3415a1402e61302bb8aaaf`.
Every member hash checked and the finite control matched exactly. This is
independent mathematical review, not a new hosted Lean verdict.

- **Same curve, same chosen place.** [Silverman VI, Corollary 5.1.1](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf#page=190)
  gives the analytic group uniformization of the original complex curve.
  At $s=-X/Y$ the literal quarter turn has derivative $i$, not
  $-i$. The resulting torus multiplication by $\pi$ has exactly
  $p$ points per fibre. Independently counting the two preimages of
  each generic abscissa, away from critical and branch values, gives
  $\max(\deg A,\deg B)=p$ for the characteristic-zero abscissa
  ratio. This does not use the degree of a residual endomorphism.
- **Correct reduction of that ratio.** Translation by $T_0=(0,0)$
  is $(-1/X,Y/X^2)$; the positive sign in the ordinate follows
  from the reflected chord. Its actual commutation implies the
  residual generic image is finite since $a+b$ is odd. At the
  same Gauss place, after primitive simultaneous scaling, the
  identity $AD=BC$ with $\bar D\ne 0$ shows $\bar B\ne 0$
  by the residue domain; reduction and cancellation do not
  increase the degree. The opposite origin-arc pole excludes a
  bounded-at-infinity ratio. Thus the separately reviewed residual
  derivative/four-unit argument applies to the same literal ratio.
- **The primary sign and all residual points.** At the same
  $Q=(i_0,1-i_0)$, the slope $-(1+i_0)$ gives
  $[2]Q=[2]JQ=T_0$. The primary condition makes the difference
  from $Q$ equal to $-2dT_0=0$. Evaluate the same generic
  equality both on $P(t)$ (abscissa pole) and on $P(t)+Q$,
  where the first abscissa increment is $2(1-i_0)t$.
  These define faithful field substitutions; the unique least
  Laurent exponent prevents any nonzero polynomial from vanishing.
  Additivity and cancellation give equality on $Q$. Coordinate
  $p$-power fixes its prime-field coordinates, and the other
  three units do not fix it. With any finite point of nonzero
  ordinate $y$, repeat the two substitutions after base extension
  using abscissa increment $2yt$. For $y=0$, use the actual
  generic point $T$ over the function field; neither $T$ nor
  $T+R$ is 2-torsion since $2(T+R)=2T\ne0$.
  Thus the subtraction proof covers all residual points, including
  identity separately, without a geometric continuation shortcut.

The result is positive coordinate Frobenius for the actual residual scalar
at the place selected by $a+b i_0=0$, over every extension of its prime
residue field. The conclusion does not itself identify the Galois
action on original torsion: the arithmetic valuation/equivariance and
prime-to-$p$ reduction-injectivity steps still have to be attached.
No class-field or prime-distribution theorem, rational point, or quartic
endpoint is certified here.

Signed: independent mathematical and evidence reviewer.
