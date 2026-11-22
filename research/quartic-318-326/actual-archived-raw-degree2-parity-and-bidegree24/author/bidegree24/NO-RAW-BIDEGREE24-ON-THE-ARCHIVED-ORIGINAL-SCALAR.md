# No raw bidegree (2,4) on the archived original scalar

Let $\beta,\delta>0$ be rational nonsquares with $[\delta]\ne[\beta]$ in the rational squareclass group, and define $f(t)=(t^2-\beta)(t^2+3\beta)$. There is no raw identity $W^2=\delta f(t)f(t')$ over a rational line $\mathbb Q(z)$ with $\deg_z t=2$, $\deg_z t'=4$. By the symmetry of the identity it also excludes $(4,2)$. This is a low-bidegree obstruction only, not a restriction on isolated rational points or on $(3,3)$ or higher degrees.

## 1. Exact branch shapes, including infinity and constant cases

Use the prior degree-two reduction, checksum-list `c6e665f9b125fbebce4e08cd3599fdb566918d3b23f8e0d961175011345eef03`. The only structural branch remaining has $t'^2=M(t)=P/Q$ of degree four, $W\in\mathbb Q(t)$, and
$$
W^2=\delta f(t)(M(t)-\beta)(M(t)+3\beta),\qquad
\mathbb Q(z)=\mathbb Q(t)(\sqrt M).
$$
Represent $P,Q$ as coprime homogeneous binary quartics; thus infinity counts with its true multiplicity. Zero $P$ or $Q$, proportional $P,Q$, and identically zero $P-\beta Q$ or $P+3\beta Q$ would make $M$ constant (or undefined), excluded by degree four. Common zeros are removed before using degree and are not allowed in this representation.

The rational line covering $t$ has exactly two geometric odd zeros or poles of $M$. Since $P,Q$ have disjoint root sets and both have even degree, one of $P,Q$ must be a rational constant times a squared binary quadratic with no odd zeros, and the other must have exactly two odd zeros. This exhausts all parity shapes, including a repeated quadratic inside a complete square and a root at infinity.

Write $A=t^2-\beta$ and $C=t^2+3\beta$ in affine notation, with the binary homogenizations understood. The odd root sets of $P-\beta Q$ and $P+3\beta Q$ are disjoint (otherwise there is a common zero of $P,Q$). The square identity forces them to partition precisely the two quadratic pairs given by $A,C$. As each fibre is rational, it takes both members of a pair or neither. Accordingly:
- if split between the two fibres, the forms are constants times one indicated quadratic times a squared linear form;
- if both pairs fall in the same fibre, that form is a constant times $AC$ and the other a constant times a squared binary quadratic.

In either case, the two rational constants $a,b$ satisfy $\delta ab\in\mathbb Q^{\times2}$. Scaling both $P,Q$ and absorbing squares into the square factors permits the normalizations below. In a combined fibre, normalize the square-side coefficient to 1, then rescale by a rational square so the coefficient of $AC$ is $\delta$. There are no other repeated-root patterns: every extra root in these fibres has even multiplicity, and their degree is already four.

## 2. Separate quadratic pairs cannot work on the literal scalar

Let $K_R=\mathbb Q(\sqrt\beta)$, $K_I=\mathbb Q(\sqrt{-3\beta})$. They are distinct quadratic fields and the rational classes becoming squares in them are respectively $\{1,[\beta]\}$ and $\{1,[-3\beta]\}$. At a root of either quadratic, a rational nonzero linear factor does not vanish; moreover $P,Q$ are both nonzero there, since $P/Q$ takes the nonzero finite value $\beta$ or $-3\beta$. If $P$ or $Q$ is a rational constant times a square, that constant must therefore match the squareclasses obtained by evaluating at these roots.

For $(P-\beta Q,P+3\beta Q)=(\delta A L^2,C S^2)$, the two evaluations of $Q$ are a square in $K_R$ and $\delta$ times a square in $K_I$. The evaluations of $P$ only multiply by $\beta$ or $-3\beta$ respectively, which are squares in their fields. Therefore for either square-side constant $c$ we require $[c]\in\{1,[\beta]\}$ and $[c/\delta]\in\{1,[-3\beta]\}$.

For the exchanged assignment $(\delta C L^2,A S^2)$ the evaluations of $Q$ have classes $[-\delta]$ and $[-1]$ in $K_R,K_I$ respectively. Those of $P$ have classes $[3\delta]$ and $[3]$; here $-\beta$ has class 3 in $K_I$. In either case, dividing by the common rational factor $-1$ or 3 leads to the same subgroup requirement:
$$[\delta]\in\langle[\beta],[-3\beta]\rangle=\{1,[\beta],[-3\beta],[-3]\}.$$
Positivity and nonsquareness leave only $[\beta]$, excluded by assumption.

## 3. Combined quadratic pairs force four odd places of M

First put both pairs over $\beta$: $P-\beta Q=\delta AC$, $P+3\beta Q=S^2$. At all four roots, $(P,Q)=(S^2/4,S^2/(4\beta))$. The evaluations cannot vanish by coprimality. The kernels of the two quadratic-extension squareclass maps intersect just at 1, forcing the normalized square side to be $P=U^2$ or $Q=\beta U^2$. If both pairs are over $-3\beta$, use $P+3\beta Q=\delta AC$, $P-\beta Q=S^2$. Now at the four roots $(P,Q)=(3S^2/4,-S^2/(4\beta))$, forcing $P=3U^2$ or $Q=-\beta U^2$ instead. Here $S,U$ denote homogeneous quadratic forms, including possible repeated roots.

Each case gives the following product of two rational quadratic forms. Over $\mathbb Q$, $A,C$ are irreducible binary quadratics. Since the two factors have degree two and multiply to the nonzero constant times $AC$, the first is $\lambda X$, the second $\mu Y$ with $\lambda,\mu\ne0$ and $(X,Y)=(A,C)$ or $(C,A)$. There is no other allocation, even if a factor has a root at infinity (the product has none). The last column gives the two roots of the other quartic expressed as values of $X/Y$:
| Both pairs over | Square side | Product of the two forms | Values of $X/Y$ for the other side |
|---|---|---|---|
| $\beta$ | $P=U^2$ | $(2U-S)(2U+S)=3\delta AC$ | $\delta/\lambda^2,\ 9\delta/\lambda^2$ |
| $\beta$ | $Q=\beta U^2$ | $(S-2\beta U)(S+2\beta U)=\delta AC$ | $(-7\pm4\sqrt3)\delta/\lambda^2$ |
| $-3\beta$ | $Q=-\beta U^2$ | $(S-2\beta U)(S+2\beta U)=\delta AC$ | $-\delta/(3\lambda^2),\ -3\delta/\lambda^2$ |
| $-3\beta$ | $P=3U^2$ | $(2U-S)(2U+S)=(\delta/3)AC$ | $(7\pm4\sqrt3)\delta/(3\lambda^2)$ |

For completeness, substitution of the sum or difference of $\lambda X,\mu Y$ for $2S$ gives, in the same row order, the other forms up to nonzero constants:
$$
\begin{split}
&\lambda^2X^2-10\delta XY+9\delta^2Y^2/\lambda^2,\\
&\lambda^2X^2+14\delta XY+\delta^2Y^2/\lambda^2,\\
&3\lambda^2X^2+10\delta XY+3\delta^2Y^2/\lambda^2,\\
&-\lambda^2X^2+(14\delta/3)XY-(\delta/3)^2Y^2/\lambda^2 .
\end{split}
$$
This also handles forms whose highest affine coefficient happens to vanish: the only way for the pullback of one linear factor in $X,Y$ to be repeated is for its ratio to be a critical value of $X/Y$.

Indeed $X/Y$ has degree two and critical values $1,-1/3$ if $(X,Y)=(A,C)$ and $1,-3$ if $(X,Y)=(C,A)$. They are the images of $t=\infty,0$, the only critical points. In the irrational rows the two ratios cannot hit either rational value. In the first row the ratios are positive, and hitting 1 would make $\delta$ a square. In the third row the ratios are negative, and hitting $-1/3$ or $-3$ would likewise make $\delta$ a square (the only factors are 1 and 9). Each pair of ratios is distinct and avoids both critical values. Thus the other homogeneous quartic has four **simple** geometric roots, as every fibre consists of two distinct points. There can be no cancellation with the squared side since $P,Q$ are coprime. This gives four odd places, contradicting the necessary two. It exhausts the combined options; no rational-conic test remains to be made in this degree.

## 4. Exact applicability to the archived original input

For the old literal $a=0$ source, the exact fixed-parameter donor `61ddafd1b2519aafd5e5b20183ea7f7b0d33577fdc4bdd1eb8d2e44c1e262003` binds $\beta=204618888056724185$, the positive $\delta=1-b/17$, and its nonsquare unit strip at 181. To distinguish $[\delta]$ from $[\beta]$, only a bounded 17-adic check is needed. On the old pinned $h,i$, both are multiples of 20 and their exact 17 depths are 1 and 2. The small $[20]R$ has formal depth one on both arms at 17, with $U([20]R)\equiv34,272\bmod289$, as verified in the exact original scalar donor `9dc74e33f8afb1fdb40aae98ed766ab5bedb8f8cb63b828c4bc04f401e9b34f5`. The point is the same fixed $[20]R$, not the newer scalar itself. Its positive-depth formal log (equivalently the unit-linear $U$ chart) gives exact norm depths 4 and 6 for the old $h,i$. The fixed source $R_s$ is a 17-unit, so $N\equiv1$, $Q_{\rm pack}\equiv0$, $W_{\rm pack}\equiv1\bmod17$ and $v_{17}(b)=2$ from the known prefactor. Therefore $\delta\equiv1\bmod17$ is a square unit whereas $v_{17}(\beta)=1$, as required. This is the same archived scalar, not a substitute or a materialization of it.

The elementary standard-library check covers the exact input depth arithmetic and the four displayed ratio discriminants. The proof above is a finite case argument, not a parameter search or an enumeration of bidegrees above (2,4).

```sh
sha256sum -c SHA256SUMS
python3 -B check_bidegree24_fixed_classes_and_rows.py | cmp - EXACT-BIDEGREE24-FIXED-CLASSES-ROWS.json
```
