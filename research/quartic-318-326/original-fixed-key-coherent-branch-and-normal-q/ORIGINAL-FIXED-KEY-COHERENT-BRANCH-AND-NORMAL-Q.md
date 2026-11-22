# Actual fixed-key detector: nonempty geometric branch and normal irregularity two

Keep the original \(a=0\) Lucas-label source with first label
\(n_0=3723\), its physical anchor, and **one fixed genuine
Gaussian-linear key** from the eventual positive contact
region. In particular this applies to a key in the certified
673 family. The contact argument, weights, genuine prime
squareclass \(\beta>1\), and original labels do not move.
The geometric variable is the coherent point on the exact
abelian surface \(\mathcal A=\operatorname{Res}_{\mathbf Q(\sqrt2)/
\mathbf Q}E\). All three detector slots have the conclusions
below, individually, for this same key. No numerical key point
or actual branch polynomial expansion is assumed.

We identify the branch line bundle after removing even
components, prove the normal double cover is geometrically
integral with \(h^1(\mathcal O)=2\), and give the exact
remaining source of possible extra irregularity on a
resolution. The smooth irregularity and the proposed marked
anti-equivariant map are **not** settled here.

## 1. The exact branch line bundle in the literal fold coordinates

In the original exact fold write \(R,I\) for its final real
and imaginary coordinate functions on \(\mathcal A\). Over
\(\mathbf Q(\sqrt2)\) the two split folded functions are
\(f_\pm=R\pm\sqrt2 I\). Because the contact key and its scale
are fixed, the nonzero constant factor in its literal square
multiplier is rational: \(17F(C_j t)\) has the genuine
squareclass \(\beta\). Thus \(B=17b=\beta\rho^2\) and
the actual \(c=\rho/17\) can be written
\[
     c=N/D,\qquad N=\kappa f_+f_-,\quad D=f_++f_- ,
     \qquad \delta=1-\beta c^2,                               \tag{1}
\]
for that fixed nonzero rational factor \(\kappa\), including
the literal \((C_jt-1)^3\) and scale factors. In particular
\(f_+f_-/(f_++f_-)\) is exactly the native trace quotient, not
a substitution of independent detector coefficients. Both
\(N,D\) are rational functions defined over \(\mathbf Q\).

Let \(P=(c)_\infty\) be the **minimal** polar divisor on
\(\mathcal A\). At each prime, its coefficient is
\(\max(0,\operatorname{ord}D-\operatorname{ord}N)\);
this cancels common divisorial factors before taking poles.
On the geometric surface let
\[
 F_\pm=(c\mp1/\sqrt\beta)_0
      =P+\operatorname{div}(N\mp D/\sqrt\beta)
                    -\operatorname{div}(D),\qquad
 G=\lfloor F_+/2\rfloor+\lfloor F_-/2\rfloor .
\]
The \(F_\pm\) have disjoint divisorial supports even though
they can meet at points. Then
\[
 \operatorname{div}(\delta)=F_++F_--2P,\qquad
 \mathcal B=F_++F_--2G,\qquad
   \mathcal L=\mathcal O_{\mathcal A}(P-G),\quad
                   \mathcal O(\mathcal B)=\mathcal L^2 .     \tag{2}
\]
Thus (2) is the exact divisor-class expression after even
components, with the two exact level divisors read from (1).
Both \(G\) and \(\mathcal B\) descend under coefficient
conjugation. There is no odd pole component. We do not
claim a numerical Néron--Severi expansion of \(P-G\);
that would require the component multiplicities of the two
literal \(N\mp D/\sqrt\beta\) after common divisorial removal.

The normalized double cover \(Y\longrightarrow\mathcal A\)
has algebra \(\mathcal O_{\mathcal A}\oplus\mathcal L^{-1}\)
with multiplication by the section of reduced branch
\(\mathcal B\). Indeed \(\delta\) is a section with divisor
\(F_++F_-\) in \(\mathcal O(2P)\); removing the square
of the effective divisor \(G\) gives the reduced section.
The resulting algebra is locally a hypersurface over the
smooth base, is normal in codimension one (simple reduced
branch and characteristic zero), and is normal by the
\(S_2\) criterion. If the reduced divisor were empty,
this same algebra would be finite étale. These claims are
about the **normal cover**, not its resolution.

## 2. The actual source forces nonempty reduced branch and geometric integrality

Work in the two real source arms, where
\[
 E:y^2=x^3-\omega^2x,\qquad D_0=\omega^2,\qquad
 U=\frac{2y}{x^2+D_0},\quad
 V=\frac{x^4-6D_0x^2+D_0^2}{(x^2+D_0)^2}.
\]
The positive constants \(\omega=3\pm\sqrt2\) are taken
on their corresponding arms. Both charts are regular
at every real point (use the limits at infinity), and
\(-1\le V\le1\), from
\(V=1-8D_0x^2/(x^2+D_0)^2\).
The first simple \(V\)-zero can be taken at
\(x=\omega(1+\sqrt2)\) with either nonzero real \(y\).
It lies in the identity component, whose real points
are the unbounded projective component. The zero is simple:
the numerator has derivative \(4x(x^2-3D_0)\ne0\)
and the \(x\)-projection is unramified there.

Here are explicit sufficient avoidance bounds for the
base Padé data, on either arm. Use degree to mean total
polar degree of a rational function on the projective
elliptic curve. The chart degrees satisfy
\(\deg U\le4,\ \deg V\le8\), by the four points over
\(x=\pm i\omega\) and the lack of a pole at infinity.
In the exact Padé formulas, with \(k,m\) the fixed source
constants, put
\[
 S=(kV/U-m)/(k^2+D_0U^2),\ 
 M=U^2 S,\quad F_V=MS,\quad a=D_0F_V^2,\qquad
 A_0=m+k^2S+D_0M,\quad B_0=k^2+mS+D_0F_V .
\]
The polar-degree bounds, using the product/sum bounds and
equality of polar and zero degrees, are
\[
 \deg S\le20,\quad \deg M\le28,\quad
 \deg F_V\le48,\quad \deg a\le96,\quad
 \deg A_0\le48,\quad\deg B_0\le68 .
\]
The common Padé logarithm is
\(kS P_G(a)/(Q_G(a)B_0)\), with \(P_G\) quadratic
and \(Q_G\) linear; its degree is at most
\(20+192+96+68=376\).
These required nonzero base functions are not identically
zero: \(A_0\) has the leading \(k^2S\) pole at the identity
(\(U=0,V=1\)), and the other required nonvanishings for the
Padé denominators and common logarithm hold at native
indices by the exact chart-domain lemmas.
Avoid \(U=0\), poles of \(S\), and zeros or poles of
\(A_0,B_0,Q_G(a)\) and the common logarithm.
That excludes at most
\[
                       4+20+96+136+192+752=1200
\]
geometric points on each arm. The real denominator
\(k^2+D_0U^2\) is always nonzero. All alternate labeled
ratios are regular at the remaining real points:
the alternate denominators other than the common
logarithm are the constant 5 or
\(Q_J(V-1)=1+5(V-1)/13\ge3/13\), and the labeled
\(U,V\) charts are real-regular.

Because \(n_0=3723\) is odd and nonzero, the map
\([n_0]\) has exactly \(3723\) real preimages of a given
point in the identity circle, all lying in that circle.
On each real arm choose one such preimage of the
displayed simple \(V\)-zero outside the at most 1200
exceptions. The first primary labeled ratio
\(U([n_0]P)A_0/(kV([n_0]P))\) has a genuine simple pole
there, since the numerator does not vanish, and multiplication
by \(n_0\) is étale. Any other primary labeled pole
on that arm has order at most one: all its real \(V\)-zeros
are simple by the same derivative test (their abscissas
are nonzero and not roots of the elliptic cubic).

Take a real path toward this pair of chosen points,
using one local parameter \(s\) on both arms.
In each split coordinate, the first ten literal leaves
are regular (real \(U,V,S,F_V\) are regular there).
In the eleventh leaf \(w_{127}+2\sqrt2 w_{128}\) is
the exact square of the first primary ratio minus the
conjugate first alternate ratio; specializing to either
arm preserves the genuine pole of order two.
Its \(w_{156}\) multiplier is a fixed nonzero key
constant because the contact is in the positive large
region. The next three leaves have pole order at most
two by their same quadratic ratio formulas. Leaf 15
has at most degree two in the singular ratios, directly
from \(w_{135},w_{136}\). Leaf 16 has degree at most
eight: \(w_{119}\) through \(w_{122}\) have degree
at most two, \(w_{123},w_{124}\) at most four, and
\(w_{137},w_{138}\) at most eight. Hence the five
successive squarings preserve strictly dominant pole
orders \(4,8,16,32,64\); the final coefficient is
positive because it is the order-two coefficient
raised to the power \(32\). Thus both
\(f_\pm=a_\pm s^{-64}+O(s^{-63})\), with \(a_\pm>0\).
There is no leading cancellation in their sum.
By (1) the trace quotient, and hence \(|c|\), is unbounded
along this real path. For small nonzero \(s\), all quotients
used are defined and \(\delta<0\).

The path lies in the same connected real component of
\(\mathcal A(\mathbf R)\) as a prepared index: the actual
indices are even and hence both orbit points lie in the
identity components. At a prepared point \(0<b<17\),
so \(\delta>0\). The positive and negative values occur
on open chart points where the double cover is split
or nonsplit as a real quadratic algebra. A finite étale
real double cover has locally constant real fibre type
over each connected component, so (2) cannot have
empty reduced branch. Equivalently, the sign change
prevents a constant-times-square description on the
coherent function field. Nonempty reduced branch gives
an odd geometric divisorial valuation; consequently
\(Y\) is geometrically integral. The negative-sign real
points are used only in this geometric proof, and are
not claimed to be Ready or indexed points.

## 3. Normal irregularity, and the exact remaining smooth correction

The actual abelian surface is simple over \(\mathbf Q\).
Over \(\mathbf Q(\sqrt2)\) its two arms admit no mutual
homomorphism, as checked for these literal curves:
the geometric twist by 7 is negated independently
of the \(j=1728\) endomorphisms. An elliptic subvariety
defined over \(\mathbf Q\) would, after splitting,
either be one factor (impossible under factor exchange)
or project surjectively to both arms, giving an
isogeny over \(\mathbf Q(\sqrt2)\), likewise impossible.

The nonempty effective \(\mathbf Q\)-rational branch is
nef and not numerically trivial. On an abelian variety,
nefness of an effective divisor follows by translating
it so as not to contain the given curve, without changing
its numerical class. Thus \(\mathcal L\) is nef and
nontrivial numerically by (2). Its associated
homomorphism to the dual abelian variety has connected
kernel defined over \(\mathbf Q\). Simplicity forces
the map to be an isogeny, so the nef line bundle
\(\mathcal L\) is ample. Therefore the normal double
cover has
\[
 h^1(Y,\mathcal O_Y)
   =h^1(\mathcal A,\mathcal O_{\mathcal A})
       +h^1(\mathcal A,\mathcal L^{-1})=2.
\]
Here the second term vanishes by characteristic-zero
Kodaira vanishing and duality on the abelian surface.
In particular the numerical expansion of (2) is not
needed to settle normal irregularity.

This does **not** equally settle the smooth model.
In successive canonical blowups of the reduced branch
at a point of multiplicity \(m\), put
\(k=\lfloor m/2\rfloor\). The new line bundle is
\(\mathcal L'=\sigma^*\mathcal L-kE\), retaining the
exceptional curve in the reduced branch exactly when
\(m\) is odd. Higher blowups treat the actual transformed
branch, including infinitely near points. With
\(\mathcal N=\mathcal L^{-1}\), one has
\(\sigma_*(\sigma^*\mathcal N(kE))=\mathcal N\)
and \(R^1\sigma_*\mathcal O(kE)\) has length
\(k(k-1)/2\) for \(k\ge1\) and zero for \(k=0\),
by the successive exceptional restrictions
\(\mathcal O_E(-j)\).
For \(k=0,1\) this step adds no irregularity.
For \(k\ge2\), the exact change of the anti-invariant
\(h^1\) is the cokernel dimension of the \((k-2)\)-jet
evaluation at the center from
\(H^0(K_{\text{base}}+\mathcal L)\).
Indeed the Leray jump is the above length minus
the loss of \(h^2(\mathcal N)\); by duality the loss is
the rank of that very jet evaluation, because
\[
     K_{\text{new}}+\mathcal L'
          =\sigma^*(K_{\text{base}}+\mathcal L)-(k-1)E .
\]
Blowing up the base does not change its own irregularity.
The finite flat cover of the resolved branch is smooth
once the reduced branch is smooth, so these exact changes
give the smooth irregularity. In particular the route to
extra irregularity is a branch point of multiplicity at
least four, possibly infinitely near, where these
adjoints fail to impose the expected independent jets.

The uncomputed geometric input is precisely the
multiplicities of the two actual finite levels after
divisorial even-part removal, their point and infinitely
near clusters, and the applicable adjoint jets at the
\(k\ge2\) centers. We have not assumed the two levels
smooth, reduced before normalization, or transverse
at their base points. Thus the normal calculation alone
cannot rule out a new elliptic quotient on the smooth
coherent cover, or decide any raw arithmetic companion.

Exact checklist dependencies:
- coherent source and literal original pole identity
  d65124d6b78d3bbdb59e015bc44c3f90c4261b5fa92e7f517e4401e98feeb5fe;
- actual detector 16-leaf formula SHA-256
  1bb3b85f8bc3ca7bd58c252ebda8b416b7011905a212a6aae7ec9c1ee5513cf5;
  actual Padé ratios SHA-256
  536503bb576c233ab948145db9d323ea5f28b5c96bacb6b1953fced45ea74244;
  literal detector gate formulas SHA-256
  5c6c61539543b60806bada94c2af35681ef98796d38e795c05ea74cb081a724d;
- audited physical Lucas labels and same original source-cell refinement
  655880673c7263d4e06b7e2556e1cae8a6a6929b238c1e118d3d608adcfe345e;
- the literal arm nonisogeny and coherent surface
  6540d554fa770d4caf5b3572c35fecc85a2bd5a02ae9872249fc7a01c88d444c;
- separate fixed-key movable-index anti-map test
  1dea5a786ccd41480689bad62f1efc795dd93a767b7507437e70d5eec9a6dc81.

No new numerical key, scan, build, or remote action.
