# First-fibre profiles for the archived genus-five cubics at 6551

Keep the hypotheses and branch-separated target frame of the [degree-preserving obstruction](../ct-original-raw-bidegree33-p6551-reduction-r1/ARCHIVED-GENUS5-P6551-BOTH-PENCILS-DEGENERATE.md), exact checksum-list `19a97eb030e4cc7179e7195a82dd38c5d9167ba753550344c66ce76c6aadea2b`. In particular, $p=6551$, $v_p(\delta)=1$ on the same archived scalar, the four geometric target branch values of $f_\beta$ have distinct reductions, and the generic marked fibres of each cubic consist of three distinct points. We work in any **one common source chart** over $K=\mathbb Q_p$ or a finite extension of odd ramification index. The degrees below refer to reduced maps **after** cancellation of the reduction holes, in the same separated target frame.

**Necessary first-level profiles.** Neither map can have reduced degree two or three. One has reduced degree zero and is constant at a target branch value. The other can have reduced degree at most one. In reduced degree one, its two holes, counted with multiplicity, must coincide at a point of its marked fibre, and all three holes of the constant map must coincide at the same point. In reduced degree zero, the possible hole profiles satisfy the exact restrictions below. This is not a classification of stable reduction trees, a sufficiency result, or an exclusion of the hypothetical family.

## 1. The entire reduced branch divisor, with multiplicities, agrees

Choose primitive integral binary cubic pairs $(A_i:B_i)$ representing the two maps, before any cancellation modulo the uniformizer. Set
$$
 F_i=(A_i^2-\beta B_i^2)(A_i^2+3\beta B_i^2),\qquad
 m_i=v_G(F_i).
$$
The values $m_i$ are finite nonnegative integers. Clearing rational denominators and taking the Gauss valuation of the square identity gives
$$m_1+m_2\equiv1\pmod2.$$
Moreover each $F_i$ has twelve simple geometric roots on the generic source projective line, including any root at infinity. The parity of the same square identity gives equality of these complete root sets. Thus the homogeneous forms are proportional by an element of $K^\times$ (compare one nonzero coefficient after proportionality over an algebraic closure). After dividing each form by the uniformizer to its respective power $m_i$, the ratio is a unit. Consequently the special divisors
$$R=\operatorname{div}(\overline{\pi^{-m_i} F_i})$$
are **identical**, as effective divisors of degree twelve on the reduced source projective line. This stronger statement retains all first-level collision multiplicities, not just the common reduced support.

Here are all the formulas for this divisor. Let $H_i$ denote the hole divisor: before cancellation factor the reduced pair by its greatest common homogeneous divisor, with multiplicity. Write $\bar\mathcal B$ for the sum of the four distinct marked points in the separated target line.

* If the cancelled pair is a map $g_i$ of positive degree $d_i$, then $m_i=0$, $\deg H_i=3-d_i$, and $R=4H_i+g_i^*\bar\mathcal B$. The coefficient of $g_i^*\bar\mathcal B$ at any point lies between 0 and $d_i$.
* If the reduced pair is a constant not in $\bar\mathcal B$ (including infinity), then $m_i=0$, $\deg H_i=3$, and $R=4H_i$.
* If the reduced pair is constant at $r\in\bar\mathcal B$, then $m_i>0$, $\deg H_i=3$, and $R=3H_i+G_i$ for an effective degree-three divisor $G_i$. Indeed this constant is rational over the residue field, so Hensel gives the unique literal branch value $\xi\in K$ reducing to it. In the separated affine frame $\bar A_i=r\bar B_i$ with $\bar B_i\ne0$. Each of the three other marked fibres has reduced cubic a nonzero scalar times $\bar B_i$, defining $H_i$. Upon passing to a field splitting the four branch values these three factors have content zero; the sole remaining factor $A_i-\xi B_i$ has content $m_i$. Its stripped cubic defines $G_i$. The common divisor and $G_i$ are rational over the residue field. All counting is over its algebraic closure; none of the divisor formulas requires a ramified extension of the Gauss parity step.

Call the map with odd $m_i$ the constant map $C$. It is of the last kind and has hole divisor $H_C$ and stripped marked fibre divisor $G_C$. The other map, denoted $O$, has even $m_i$.

## 2. The nonconstant possibilities

If $O$ has positive reduced degree $d$, a point of $H_C$ has multiplicity at least 3 in $R$. For $d=2$ no such point can lie outside $H_O$, since the marked pullback there has coefficient at most 2. But $H_O$ then has degree one, say $H_O=P$; hence $H_C=3P$. On the $O$ side the coefficient at $P$ is at most $4+2=6$, whereas the $C$ side needs at least 9. This rules out reduced degree two in either pencil, even though both can be degenerate.

If $d=1$, again $H_C$ is supported on $H_O$. If $H_O$ consists of two distinct points, each can carry at most $4+1=5$ in $R$, hence at most one in $H_C$, a contradiction to degree three. Thus $H_O=2P$, $H_C=3P$. The required multiplicity at $P$ forces the degree-one map $g_O$ to send $P$ to a marked point: $8+1=9$ exactly. The divisor $G_C$ is precisely the other three simple marked preimages under $g_O$, none equal to $P$.

For completeness, if $d=3$ the same divisor comparison is a short form of the earlier Riemann--Hurwitz argument. There are no $O$ holes and the coefficients of $R$ are at most three. Hence $H_C$ must consist of three distinct points, each a triple marked preimage under the separable tame cubic $g_O$. The ramification contribution is at least six instead of four.

## 3. The constant possibilities

If $O$ is constant at a nonmarked point, then $4H_O=3H_C+G_C$. At each point in $H_O$ the $H_C$ multiplicity is at most the integer part of the product of $4/3$ and the $H_O$ multiplicity, and $H_C$ has no support outside $H_O$. For $H_O$ of geometric shape $(1,1,1)$ or $(2,1)$ these upper bounds equal the multiplicities in $H_O$; equality of the degrees gives $H_C=H_O$. For shape $(3)$ the sole support already forces the same equality. In all cases $G_C=H_O=H_C$.

If instead $O$ is constant at a marked point (with positive even content), use
$$3(H_C-H_O)=G_O-G_C.$$
If $H_C=H_O$, this gives $G_C=G_O$. Otherwise the positive and negative parts of $H_C-H_O$ have equal positive degree, which is at most one because each $G_i$ has degree three. Thus there are distinct residue-rational points $P,Q$ and a common effective degree-two divisor $H$ such that
$$
 H_C=H+P,\quad H_O=H+Q,\qquad G_C=3Q,\quad G_O=3P.
$$
The degree-one parts are rational because $H_C-H_O$ is rational. This last statement allows $H$ to contain $P$ or $Q$ and applies even if the two branch-constant values coincide.

Only these first-reduction restrictions are asserted. Coinciding reduced roots are kept with multiplicities. The analysis says nothing about further blowups, tangent directions or distances of clustered roots, and gives neither sufficiency of a surviving profile nor a pointwise obstruction. No new prime or scalar was tested.
