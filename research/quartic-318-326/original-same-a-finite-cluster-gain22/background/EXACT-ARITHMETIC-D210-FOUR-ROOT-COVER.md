# Exact arithmetic twists of the original discriminant-210 curve

On the literal original \(t=32s\) line, the actual maximal discriminant-210
Shimura curve has function field
\[
\boxed{\;\mathbb Q(t)\left(
 \sqrt{-14\,t},\ \sqrt{-6(t-32)},\
 \sqrt{42(t-76832)},\ \sqrt{-21(t+343)}
 \right).\;}
\]
This is an arithmetic comparison over \(\mathbb Q\), not just the
complex completed four-root curve, and not an assertion that the
normalization of a naïve integral four-root equation is a fine PEL model.

## 1. Recover five exact arithmetic covers

The prior literal branch calculation, from González–Rotger
[Theorem 4.2, Tables 2 and 3, and Proposition 5.2](https://web.mat.upc.edu/victor.rotger/docs/ShimuraGenusOne.pdf),
gives the following matched row:
\[
(b_0,b_1,b_2,b_3,b_4)=(0,32,76832,-343,\infty),\qquad
(\sigma_0,\sigma_1,\sigma_2,\sigma_3,\sigma_4)
=(w_{105},w_{70},w_{42},w_{30},w_{210}).
\]
The four finite labels are a basis of \(W\simeq \mathbf F_2^4\), and
\(\sigma_4=\sigma_0+\sigma_1+\sigma_2+\sigma_3\).
Let \(\chi_j\) be the character that is zero at exactly \(\sigma_j\)
and nonzero at the other four listed inertia labels. It is a character
because their single relation has four ones. Write \(H_j=\ker\chi_j\).
Squarefree-divisor multiplication gives this exact decoder:

| Omitted \(t\) | \(H_j\) (Atkin–Lehner subscripts) | Actual \({\rm Jac}(X/H_j)\) |
|---|---|---|
| \(0\) | \(3,5,7\) | 210b6 |
| \(32\) | \(2,5,7\) | 210c3 |
| \(76832\) | \(2,3,7\) | 210a6 |
| \(-343\) | \(2,3,5\) | 210e5 |
| \(\infty\) | \(6,10,14\) | 210d2 |

The last column is the exact **isomorphism class over \(\mathbb Q\)**,
not the isogeny class or geometric \(j\)-invariant. Its source is
Padurariu–Saia [Theorem 1.2(1), arXiv:2509.25368v2](https://arxiv.org/pdf/2509.25368v2#page=2)
and the five \(D=210,N=1\) rows of [Table 2, p. 33](https://arxiv.org/pdf/2509.25368v2#page=34).
Each residual double cover \(X/H_j\to X/W\) has the *other* four
branches, of index two. Each rational branch has a single geometric
point above it, hence that point is rational. Use the point over
\(t=\infty\) as origin in the first four rows and the point over \(t=0\)
in the last. This makes \(X/H_j\) the displayed elliptic curve over
\(\mathbb Q\), and the residual deck involution is \([-1]\) (a
nonidentity involution fixing the origin of a characteristic-zero
elliptic curve). Thus its invariant coordinate is the usual
Weierstrass \(x\), not an unknown hyperelliptic involution.

## 2. Rational coordinate and square factors

For each [Cremona exact model row](https://raw.githubusercontent.com/JohnCremona/ecdata/master/allcurves/allcurves.00000-09999),
complete the square \(Y=y+(a_1x+a_3)/2\), so \(Y^2\) is a monic cubic
whose three finite roots are rational. The \(\mathbb Q\)-linear
fractional comparison of base coordinates must send the chosen
branch origin to \(\infty\). It is therefore \(x=A t+B\) in the first
four rows and \(x=A/t+B\) in the fifth. Matching the three finite
roots in each case leaves a **single** affine transformation among
the six assignments, exactly this one:

| Curve | Roots of completed cubic | \(A\) | \(B\) | Literal Kummer constant | Class |
|---|---|---:|---:|---:|---:|
| 210b6 | \(-345/4,-85,171\) | \(1/300\) | \(-6383/75\) | \(1/27000000\) | \(3\) |
| 210c3 | \(-77/4,-19,37\) | \(1/1372\) | \(-19\) | \(1/2582630848\) | \(7\) |
| 210a6 | \(-34,-26,239/4\) | \(-1/4\) | \(-26\) | \(-1/64\) | \(-1\) |
| 210e5 | \(-801/4,-200,400\) | \(1/128\) | \(-801/4\) | \(1/2097152\) | \(2\) |
| 210d2 | \(-6,2,11/4\) | \(-19208/75\) | \(601/300\) | \(-16807/843750\) | \(-42\) |

In the first four rows one simply substitutes \(At+B\), obtaining
\(A^3\prod_{i\ne j,\,i<4}(t-b_i)\). In the last row multiply the cubic
after substitution by \(t^4\) (i.e. use \(Y'=t^2Y\)). It is
\(-A^3/(b_1b_2b_3)\) times \(\prod_{i<4}(t-b_i)\).
This retains the sign and rational square factor, not just the roots.
The checker reconstructs each completed cubic from its five pinned
Cremona coefficients, then verifies the exact coefficient identity of
all five transformed equations.

## 3. Recover the four one-root characters

Let \(\epsilon_i\) be dual to the four finite inertia labels.
Over \(\mathbb Q(t)\) its one-root squareclass has the form
\(c_i(t-b_i)\) with \(c_i\in\mathbb Q^\times/(\mathbb Q^\times)^2\):
only \(b_i\) and infinity have odd exponents, and other irreducible
finite factors have even exponents by their simple geometric roots.
The previous rows compute
\[
[k_j]=\prod_{i\ne j}[c_i]\ (j<4),\qquad
[k_4]=\prod_{i<4}[c_i].
\]
Thus \([c_j]=[k_jk_4]\), giving \((-14,-6,42,-21)\).
Each product with the displayed representatives differs from its
appropriate \(k_j\) by exactly the common square \(42^2\). The
four dual characters are independent, so their genuine fixed
quadratic fields generate the whole arithmetic function field.
Uniqueness of the smooth proper normalization identifies the
same whole curve over \(\mathbb Q\) over the **same** quotient
coordinate \(t\). The change of sign of an individual square root
is precisely its deck coordinate choice; it is not a new twist.

For any nonbranch rational \(t\), this gives explicit coarse point
fields inside the normal level-three field obtained earlier. The
only fixed rational prime support from the four constants is
\(2,3,7\). At an odd prime outside the original bad support, if
\(t\) is integral and each contacted depth is even (including
zero), every square root is unramified; if \(t\) has a pole of even
depth, each \(t-b_i\) has that same even depth, and the assertion
also holds. This is a direct coarse-field check only. Good reduction
of the lifted surface, existence of fine markings, 3/11 integral
chart identification, the stable Hodge degree and arithmetic Yuan
KS normalization are separate. None is inferred from this generic
function-field computation. No Lean execution was requested or run.

Reproduce the finite rational checks with
`python replay_d210_twists.py | cmp - EXACT-D210-TWISTS.json`. The
small Lean source only encodes the four constants and verifies the
five square ratios, not the externally pinned quotient identities.
