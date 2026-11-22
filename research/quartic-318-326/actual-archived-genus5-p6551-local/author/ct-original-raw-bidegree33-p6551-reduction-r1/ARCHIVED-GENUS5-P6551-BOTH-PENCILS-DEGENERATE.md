# Both archived genus-five cubic maps must degenerate at 6551 in the separated target frame

Set $p=6551$, $\beta=204618888056724185$, $f(t)=(t^2-\beta)(t^2+3\beta)$, and use the same archived scalar $\delta=1-b/17$. The [published exact archived row](https://github.com/doublemover/diophantine-z-q/blob/f767adfb8eba61b98fc865e82f73776f4f095799/research/quartic-318-326/actual-scalar-specialization/ACTUAL-THETA-MODULAR-ROWS.md) gives $v_p(\delta)=1$ (stripped residue $684$). The fixed $\beta$ is a $p$-unit ($\beta\equiv1452$); $p$ does not divide $6$. Thus the four geometric branch points $\{\sqrt\beta,-\sqrt\beta,\sqrt{-3\beta},-\sqrt{-3\beta}\}$ have distinct reductions.

**Claim.** Suppose rational cubic maps $t,t'$ and a rational function $W$ satisfy $W^2=\delta f(t)f(t')$ in the genus-five stratum: neither map is critical above these four branch values. On the source projective line, after *any* projective coordinate change over $\mathbb Q_p$, neither map has degree-preserving good reduction into the stated projective target line. The same is true over every finite extension of odd ramification index and in every target frame in which the four branch points still have distinct reductions. Both maps must degenerate in this sense, not merely at least one. This is a local reduction constraint on the genus-five stratum, not an exclusion of the family.

## 1. Clearing denominators in an arbitrary source frame

Let $K/\mathbb Q_p$ be a finite extension of odd ramification index, $v$ its uniformizer-normalized valuation, and $k$ its residue field. Choose any $K$-coordinate on the source and write the maps as coprime homogeneous cubic pairs $(A:B)$ and $(A':B')$. Independently scale each pair by a nonzero constant so all coefficients are integral and some coefficient of each pair is a unit. This applies after every source change: the homogenized pair remains coprime over $K$, and no division by a factor common only modulo the uniformizer is made. Such a factor is recorded as a reduction hole, meaning a common zero of the two reduced forms.

Write $F(A,B)=(A^2-\beta B^2)(A^2+3\beta B^2)$. Dehomogenizing on the chosen source coordinate, the equation is
$$
 (WB^2 B'^2)^2 = \delta F(A,B)F(A',B').
$$
All relevant quantities are rational functions; poles in the affine chart do not matter. The Gauss valuation on $K(z)$, equal to the least coefficient valuation on a polynomial and extended multiplicatively to quotients, gives
$$
 v_G(F(A,B))+v_G(F(A',B'))\equiv 1\pmod 2,
$$
as $v(\delta)$ is odd. The two valuations in this sum are nonnegative. Homogeneous forms reduced this way still record the root at infinity; taking the affine coefficient list for the Gauss valuation does not discard any coefficients.

For a primitive pair $(A:B)$ of degree three, $v_G(F(A,B))>0$ exactly when the reduced pair is proportional with constant value a branch point. Indeed, the reduced forms are not both zero, and the product of the two quadratic forms in $\bar A,\bar B$ is zero in $k[X,Y]$ exactly when one factor is the zero polynomial. Over $\bar k$ this forces $\bar A=r\bar B$, where $r$ is one of the four distinct finite branch roots. Necessarily $\bar B\ne0$ in this case. A good cubic reduction in the literal frame means that its primitive reduced forms have no common zero on $\mathbf P^1_{\bar k}$, and in particular it gives Gauss valuation zero for $F$.

## 2. Three forced totally ramified points cannot fit in a cubic

Suppose $t$ has good reduction in the chosen frame. The parity and preceding observation imply that the reduction of $t'$ is constant, equal to one branch root $r$, and all its holes are zeros of the single cubic $\bar B'$. Pass freely to an algebraic closure for counting and reduction of geometric points. Three other target roots have reductions distinct from $r$. Each of their fibres under $t'$ is a triple of distinct geometric points by the genus-five hypothesis; for any such target root $y$ the reduced equation $\overline{A'-yB'}=(r-\bar y)\bar B'$ forces all three points of the fibre into the holes of $t'$. Thus nine distinct geometric points specialize into at most three points on the reduced source.

The two branch sets on the source agree. In fact $F(A,B)$ and $F(A',B')$ each have twelve distinct geometric zeros, with no contribution from the poles of $t,t'$ to the parity of $f$; the square identity equates their odd supports. Hence the nine points also belong to the four marked fibres of $t$. Since $t$ has good reduction and the four branch values have different reductions, all generic branch points specializing to a given hole of $t'$ must belong to a *single* one of these fibres of $t$. There are at most three in each. Therefore there are exactly three holes carrying three branch points each.

The good cubic reduction of $t$ then has local degree three at each of these holes. To see it directly, for the corresponding marked root $x$ the cubic $A-xB$ has primitive integral reduction (the reduction of $t$ is nonconstant); its three generic roots all reduce to the hole. After a finite splitting extension, write this homogeneous cubic as a product of primitive integral linear factors times a unit. Primitivity of the product follows by reduction in the domain $\bar k[X,Y]$. The reduced cubic therefore has a triple root at that hole, and $\bar A,\bar B$ have no common zero there. This proves the local degree claim including a possible hole at infinity.

The reduced cubic map is separable as its degree is three and the residue characteristic exceeds three. Each of its three local degrees three contributes $3-1=2$ to tame Riemann--Hurwitz for $\mathbf P^1\to\mathbf P^1$, but the total allowed is $2\cdot3-2=4$. This contradiction rules out good reduction of $t$. Exchange the two maps to rule out good reduction of $t'$.

## 3. Scope of target coordinates and of the obstruction

A projective target change that keeps the four branch reductions distinct belongs to $\operatorname{PGL}_2(\mathcal O_K)$. To see this, choose a primitive integral matrix representative of the change. If its determinant is not a unit, the reduced matrix has rank one and collapses all reduced points except possibly its single kernel point. At least three of the previously distinct branch points then have the same reduction in the new frame. The stated branch-separated changes are therefore exactly the integral projective automorphisms, under which a map's degree-preserving good reduction is unchanged. The assertion about each pencil allows a different arbitrary source coordinate for each test, since the proof works in every source coordinate separately. It does not assert the same for a nonintegral target reframe that clusters the branch values.

The argument uses odd ramification index essentially in the Gauss parity. It does not classify the simultaneous bad-reduction types, rule out a solution that degenerates at this place, or treat the eight-branch genus-three stratum. It uses only the already certified 6551 place and no search over primes, parameters or cubic pencils.
