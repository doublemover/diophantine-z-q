# All 5,376 marked flags in the helper-673 parity receiver

The fixed local helper $I=673$ has 56 supersingular geometric $j$-invariants and 96 literal cyclic-48 flags per curve. This table identifies **all** 5,376 flags with their exact level-chart points and with one rigid-frame lift in the basis of the fixed degree-17/Frobenius transport file. It supplies the actual weights for the finite mod-two coefficient. It does not supply the unknown moving prime operators or an actual aggregate value.

## 1. Bind subgroups, not just their underlying curve

The long chart is $Y^2=X^8+14X^4+1$ with $y_{48}=(Y+X^4+1)/2$. Use the ordered level functions
$$
       t_{16}=X-2+3X/y_{48},
       \qquad t'_{16}=(y_{48}-2X-1)/X .
$$
The first forgets the 3-subgroup and the second forgets it **after its quotient**, not after changing the 16-level orientation. These are the exact two maps of [Colò, Appendix A](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf). Compute the underlying $j$ by the successive replacements $t\mapsto t^2/(t+d)$ for $d=2,4,16$ and then $t\mapsto(t+256)^3/t^2$. The replay checks the ordered pair together with $j$ is injective on the full supersingular chart, after enumerating affine $X,Y$ in $\mathbf F_{673^2}$. The omitted $X=0,\infty$ are cuspidal, as are any excluded forgetful denominator branches; no good CM point has a cusp reduction.

Independently, on each of the 56 elliptic curves now use its exact stored 32-basis and 3-basis. The cyclic 16-subgroups are represented by $P_{16}=[2]Q$ with $Q$ having coefficients $(1,b)$ for all $b\bmod16$, and $(a,1)$ for even $a\bmod16$. They are all 24 projective lines over $\mathbf Z/16$. The four nonzero projective lines of 3-torsion are treated in the same way. Evaluate the 16-function directly from the generator of each of these subgroups, before and after the degree-three Vélu quotient, on the pushed-forward 16-generator. This gives the ordered pair of the exact moduli correspondence, without matching by $j$ alone.

For clarity the subgroup formula used is the exact $t_8$ receiver from the lower chart. Given $P$ of order 8 on $y^2=x^3+Ax+B$, put $e=x(4P)$, $B'=3e^2+A$, $u=x(2P)-e$, and $v=x(P)-e$. The involutive first quotient has $u^2=B'$; the normalized quotient abscissa coordinate is $k=(v+B'/v)/u$, and $t_8=32/(k-6)$. For the order-16 generator use $t_8$ of its double, and the $t_8$ of its image after quotient by its point of order 2. The two scalar equations for $t=t_{16}$ are
$$
             t^2/(t+2)=h_0,\qquad t(t+4)=h_1.
$$
The second is the opposite order-two-root branch followed by the $t_8$ forgetful map; it is the same checked formula used for the earlier exact inert-chart receiver. The replay requires a unique simultaneous root. It matches all 96 subgroup pairs per $j$ to distinct chart points, reaching all 5,376 chart points. It also records for each the explicit $(Q,V,Z)$ frame choice in the already bound matrices; $V$ is chosen independent of $16Q$ in the very same basis. No unlabelled supersingular $j$ is substituted for a framed target.

## 2. Actual finite weights and orbit counts

Fix the $\sqrt3$ residue $26\bmod673$. Put $x=y_{48}/X^2$, $t=X-1/X$, $y=tx$ as in the literal elliptic quotient. The receiver value
$$
   H(X,Y)=y/(x-3)-(2+\sqrt3)
$$
is computed on each named orbit. The replay checks both the exact Fricke relation of these function values and their Frobenius relation. The Fricke formula is $w(X,Y)=((X+1)/(X-1),4Y/(X-1)^4)$. Frobenius is field conjugation on the chart.

There are 1,368 orbits under $F,w$. The exact bins are:

| Orbit type | Weight even | Weight odd |
|---|---:|---:|
| Four distinct labels | 616 | 704 |
| Two labels, $F=w$ | 24 | 24 |
| Frobenius fixes the individual label | 0 | 0 |

For the four-label case the weight is the nonsquare bit of $N_{\mathbf F_{673^2}/\mathbf F_{673}}H$; for the two-label case it is the nonsquare bit of $H$ in $\mathbf F_{673}$. These are the weights for the **unsigned** mod-two count, not a count of classes or distinct weighted terms with multiplicities already included. The output records one representative, its weight and its exact usable rigid frame for every orbit. The source table and field arithmetic are SHA-bound to the existing 56-curve fixed operator, so there is no basis conversion ambiguity across these two finite donors.

The conditional test is the sum of these weights times the corresponding exact rigid product entry, taken modulo two. The table has both possible weights, so it is not an identity claiming the sum is zero or nonzero. No first-arm $n$, new contact key, final point, or rank has been evaluated.
