# The literal \(t=18\) square-match surface is of general type

The input-zero labels, anchor and fixed \(t=18\) first point are unchanged. The claim is for the optional **plus-sign** degree-two specialization gate, not the complete secant equation or a new index. We compute a big canonical divisor on a resolution of its exact double cover. This does not assert nondensity of rational points or finiteness of native matches.

## 1. The branch line bundle

Use the restriction-of-scalars surface \(\mathcal A=\operatorname{Res}_{\mathbb Q(\sqrt2)/\mathbb Q}E\) from the preceding paper, and work geometrically on \(E\times E^\sigma\). Let \(x,y\) be its normalized degree-eight arm functions. On the first arm the geometric branch values of \(x\) are \(0,\infty,\pm1/(R_s\omega)\), where \(\omega=3-\sqrt2\), \(R_s=4376874610839020\); the conjugate formula holds for \(y\). All points over 0 or infinity have ramification index two, four per fibre. The value \(-1\) is unramified on both arms, with eight points per fibre. These follow from \(x=1/(R_s x_E([2]P_1))\), the analogous conjugate identity, and characteristic zero.

Write the scalar as \(c=\lambda J\), where
\[
 J=(1+x)^2(1+y)^2+\frac{\gamma}{xy},\qquad
 \lambda=\frac{12}{1+114444R_s},\qquad \gamma=\frac{I_s^2}{R_s^{31}}>0.
\]
The polar divisor \(P\) of \(J\) consists of \(x=0\), \(y=0\) with their orders in the arm functions, and \(x=\infty\), \(y=\infty\) with twice those orders. More precisely, if \(D_{x,0},D_{x,\infty}\) are the respective degree-eight divisors on \(E\), and similarly for \(y\) on \(E^\sigma\), then
\[
 P=p_1^*(D_{x,0}+2D_{x,\infty})+p_2^*(D_{y,0}+2D_{y,\infty}).
\]
Hence \(L=\mathcal O(P)\) has bidegree \((24,24)\), is ample and has \(L^2=1152\). The two branch levels \(t_1,t_2\) are the distinct nonreal roots of \(Q(\lambda t)=(2a_{\rm sec}\lambda t+2A)^2+B_0(\lambda t)^2\) with \(A,B_0>0\). Both are nonzero. The zero divisor of \(Q(c)\), taken as a section of \(L^{\otimes2}\), is the reduced branch divisor computed in the preceding paper. It consists of the two closed level curves of \(J\), with no boundary component. Thus \(L\) is the double-cover branch line bundle. The normalization is the usual double cover for this data: the branch is reduced so the local double hypersurface is regular in codimension one and satisfies \(S_2\). Amplitude of the canonical bundle on this normal model alone would not prove the assertion on a resolution.

## 2. Boundary: all nonzero canonical corrections

Downstairs in the \(x,y\) coordinates, the level equation on the torus is
\[
              xy((1+x)^2(1+y)^2-t)+\gamma=0.
\]
Its bidegree-\((3,3)\) closure meets the boundary only at \((\infty,0),(0,\infty),(\infty,-1),(-1,\infty)\). In detail, the \(x=0\) row is nonzero for finite \(y\), the \(x=\infty\) row is represented by \(y(1+y)^2\) for finite \(y\), and at \((\infty,\infty)\) the leading coefficient is nonzero; apply the same argument with coordinates exchanged.

At \((\infty,0)\) put \(a=1/x,\ b=y\). The local equation for either \(t\) is
\[
 F_t(a,b)=b(1+a)^2(1+b)^2-t a^2 b+\gamma a^3=0.
\]
The derivative in \(b\) is a unit at the origin, so the solution has \(b_t(a)=-\gamma a^3+O(a^4)\). Subtracting the two equations, and using the same unit derivative in the divided difference in \(b\), gives exact order 5 for \(b_{t_1}(a)-b_{t_2}(a)\): the difference of the equations before varying \(b\) is \(-(t_1-t_2)a^2b\), with leading coefficient nonzero. At each lifted geometric point take parameters \(a=u^2,b=v^2\), possible since both arms ramify simply. Each level splits into two smooth graphs \(v=\pm u^3\sqrt{b_t(u^2)/u^6}\). Across the two levels, opposite signs have contact order three; equal signs have contact order seven (the squared graphs differ to order ten, while their sum at equal signs has order three). There are four branches at the point. On successive blowup charts \(v/u, v/u^2, v/u^3\) they remain four at one point for exactly three multiplicity-four centres, after which they split into two pairs. Only multiplicity-two centres remain. The same holds at \((0,\infty)\). This type occurs at \(2\cdot4\cdot4=32\) geometric points of \(\mathcal A\).

At \((\infty,-1)\), use \(a=1/x,\ b=1+y\); the equation is
\[
 (b-1)(1+a)^2 b^2-t a^2(b-1)+\gamma a^3=0.
\]
Only the first arm ramifies, so \(a=u^2\) and \(b\) is a parameter. For \(b=u^2 w\) the stripped equation at \(u=0\) is \(t-w^2=0\). It has two simple roots, so each level has two smooth graphs \(b=u^2(\pm\sqrt t+O(u))\); the degree-two initial term in \(b\) accounts for both local branches. The four leading constants from the two levels are distinct. There are exactly two successive multiplicity-four centres and then the branches are disjoint. This also holds at \((-1,\infty)\), for \(2\cdot4\cdot8=64\) geometric points in total.

No exceptional divisor enters the new branch in these blowups, since the multiplicities used are even. In particular the distinct-pair corrections do not create additional branch intersections with exceptional divisors.

## 3. Torus: at worst crepant singularities

The two branch levels do not intersect on the torus. A critical point of \(J\) there has \(x=y=z\) with \(2z^3(1+z)^3=\gamma\). At such a point the Hessian has diagonal entries \(2(1+z)^2(3+2/z)\) and off-diagonal entries \((1+z)^2(6+2/z)\). Its eigenvalues are its diagonal entry plus or minus the off-diagonal entry. Neither is zero: \(z=0,-1\) is excluded and the other candidate \(z=-1/2\) gives \(\gamma<0\). The diagonal entry is nonzero as well, since \(z=-2/3\) similarly gives \(\gamma<0\). Thus away from arm ramification an interior singularity is an ordinary node, if present at all.

At a point with exactly one ramified arm, take \(x=x_0+u^2\) after exchanging the arms if needed. If \(J_y\ne0\) the branch is smooth. If \(J_y=0\) but \(J_x\ne0\), the local branch equation is formally equivalent to \(U^2+V^j=0\), for \(j=2\) or 3: its restriction to \(x=x_0\) has zero of order at most three by the fibre cubic; the coefficient multiplying \(u^2\) in the difference before restriction is a unit, absorbable in \(U\), and the remaining leading unit is absorbable in \(V\). If both derivatives vanish, complete the square formally in the \(y\)-direction, using \(J_{yy}\ne0\). The residual term in \(x-x_0\) has order two because the full Hessian is nonsingular. Substituting \(x-x_0=u^2\) gives \(V^2+U^4=0\) after absorbing its unit. At a doubly ramified torus point both arm values are real, so the value of \(J\) is real and cannot equal either nonreal branch level.

Since the other branch level is a unit at each of these torus points, the possible singular double covers there are precisely of type \(z'^2=U^2+V^j\) in formal coordinates, with \(j=2,3,4\), up to exchange of variables. These are the rational double points \(A_{j-1}\) and have a crepant resolution. Thus torus singularities entail no nonzero canonical correction, regardless of whether any of their finite locations belongs to the literal levels.

## 4. Bigness after resolution, and the arithmetic theorem still absent

For a blowup \(\rho\) of a branch point of multiplicity \(m\), use the new branch line \(\rho^*L-\lfloor m/2\rfloor E_{\rm exc}\). The sum of the base canonical divisor and branch line therefore changes by \((1-\lfloor m/2\rfloor)E_{\rm exc}\) relative to pullback. Its square decreases by one at each multiplicity-four centre and does not change at multiplicity two. With the boundary resolved, let \(A'\) be the blown-up base, \(D=K_{A'}+L'\), and \(N\) the total pullback of the original \(L\). The calculations give
\[
  D^2=1152-32\cdot3-64\cdot2=928,\qquad D\cdot N=1152,\qquad K_{A'}\cdot N=0.
\]
All these intersection identities use total-transform classes, or equivalently apply one blowup at a time. The pullback \(N\) is nef. Thus \(K_{A'}-mD\) cannot be effective for \(m>0\) (negative intersection with \(N\)), and Riemann--Roch gives quadratic growth of \(h^0(A',mD)\). In particular \(D\) is big. The canonical divisor of the resulting normal double cover is its pullback; the residual torus resolution is crepant. This proves that a smooth projective resolution of the original surface is of general type. All calculations can be made over the algebraic closure; they determine the geometric Kodaira dimension of a resolution over \(\mathbb Q\) as well.

The required square at an admissible source index is still a **rational point over \(\mathbb Q\)** over the exact native orbit point. These chart points are in the smooth étale locus of the double cover, since \(c(h)\) is finite and \(Q(c(h))>0\). An infinite set of distinct such indices has Zariski-dense image in \(\mathcal A\), by the preceding orbit-independence and curve argument. Its lifted points must then be Zariski dense in the smooth projective surface too: a proper closed set has dimension at most one and cannot map onto the two-dimensional base.

Accordingly rational-point **nondensity for this particular surface**, for instance the conclusion of weak Bombieri--Lang over \(\mathbb Q\) applied to it, would imply finiteness of these optional plus-sign matches. Nondensity just for points above the native orbit would already suffice. General type is not a proof of either nondensity assertion. Even a finiteness theorem would not exhibit a matching \(h\), exclude all of them, or decide the unrestricted secant equation.

Exact predecessor: literal square cover checksum-list SHA-256 6540d554fa770d4caf5b3572c35fecc85a2bd5a02ae9872249fc7a01c88d444c and paper SHA-256 54bec9af435d72a51ebbc1d6206d17ea429d0c5f490f38aef26fb66fd816192f. No numerical index, coefficients \(I_s\), prime search, or rational-point solver is used here.
