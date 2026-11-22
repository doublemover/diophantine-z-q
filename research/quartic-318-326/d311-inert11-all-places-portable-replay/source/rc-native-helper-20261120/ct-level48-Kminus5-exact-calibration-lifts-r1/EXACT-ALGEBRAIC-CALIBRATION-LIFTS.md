# Exact algebraic lift specifications for all 32 fixed cubic calibration flags

This is fixed arithmetic on the **actual** eight-row real CM calibration over $\mathbb Q(\sqrt5,\sqrt6)$, whose complete packets use $K_*=\mathbb Q(\sqrt{-5})$. It supplies exact integer class polynomials and an unambiguous characteristic-zero algebraic specification for every one of its 32 distinct fixed flags. It is not a toy choice of an auxiliary chart nor a new moving conductor. It does not materialize the algebraic 241-dual quotient/isogeny library, provide a moving signed intersection valuation, evaluate the CM product, or prove a point.

## 1. Exact class equations without complex rounding

Compute the monic symmetric $\Phi_l(X,Y)$ for $l=2,3,5$ from the integer Laurent series

$$j(q)=\frac{(1+240\sum_{m\ge1}\sigma_3(m)q^m)^3}{q\prod_{m\ge1}(1-q^m)^{24}}.$$

Set $d=l+1$. Use symmetric monomials of bidegree at most $(d,d)$ with the $X^d,Y^d$ top coefficient condition (already known for the classical modular polynomial), and vanish on $(j(q),j(q^l))$ through exponent $2d^2$. A nonzero difference would be a meromorphic function on $X_0(l)$ of total polar degree at most $2d^2$ (each projection has degree $d$); the tested vanishing at this one cusp makes such a difference zero. The exact linear system in the replay has a one-dimensional solution and all coefficients of its monic vector are integral. The input Laurent cut at 175 has ample slack above all exponents: for $l\le5$, forming the powers and dilated products needs no terms higher than $2d^2+ld+d\le108$ in the undilated factors. All polynomial resultant and factor operations are rational/integer exact.

The diagonal $\Phi_5(X,X)$ has a unique irreducible degree-two factor. A diagonal root is a complex elliptic curve admitting a cyclic degree-five endomorphism, whose trace $t$ gives discriminant $t^2-20$ for $|t|\le4$. All the other resulting quadratic orders ($-19,-16,-11,-4$ and overorders) have class number one. The two classes of discriminant $-20$ are exactly the order admitting the pure $\sqrt{-5}$. Thus the degree-two factor is $H_1=X^2-1264000X-681472000$, the maximal-order class polynomial of $K_*$. For $H_f=H_{-20 f^2}$ compute the remaining polynomials using exact resultants:

| $f$ | Resultant before division | Divisor |
|---:|---|---|
| 2 | $\operatorname{Res}_X(H_1(X),\Phi_2(X,Y))$ | $H_1(Y)$ |
| 3 | $\operatorname{Res}_X(H_1(X),\Phi_3(X,Y))$ | $H_1(Y)^2$ |
| 4 | $\operatorname{Res}_X(H_2(X),\Phi_2(X,Y))$ | $H_1(Y)^2$ |
| 6 | $\operatorname{Res}_X(H_2(X),\Phi_3(X,Y))$ | $H_2(Y)^2$ |
| 12 | $\operatorname{Res}_X(H_4(X),\Phi_3(X,Y))$ | $H_4(Y)^2$ |

Here 2 is ramified in $K_*$, so at conductor 1 it has one horizontal edge and two descending edges; at conductor 2 there is exactly one ascending edge and two descending, with two ascending target occurrences per old class. The prime 3 splits in $K_*$ and in these three uses has two horizontal neighbours at the source conductor and two descending edges. Each descending endpoint is counted once (it has a unique reverse ascending kernel). These facts give the displayed divisors with exact multiplicity even if there is coincident horizontal $j$. The resulting degrees are $2,4,4,8,8,16$ for $1,2,3,4,6,12$. The replay also checks the same polynomials at every ordinary $K_*$ volcano vertex for the exact finite source.

## 2. The exact marked algebraic branch at 29

Let $q=(X_0,Y_0)$ be a fixed flag appearing in the eight signed real packets, with the existing encoding $a+29b$ for $a+b\sqrt2$ in characteristic 29. The 32 actual flags, not an unmarked list of ordinary $j$'s, have source/target conductor pairs $(4,4)$, $(12,4)$ and $(4,12)$ with counts 16, 8 and 8 respectively. The replay pins the exact corrected real calibration manifest `c763e955648ab6ecc2873fdf2250e69478270cc6cf07a7b63d0c87f5aa528517` and checks each constituent hash. Define $P_q$ to be the unique algebraic root with the named reduction $q$ of the two equations

$$Y^2-X^8-14X^4-1=0,\qquad H_{f_A}
      \bigl(j_{48}(X,Y)\bigr)=0,$$

where $j_{48}$ is the literal Colò forgetful function and $f_A$ is the computed source conductor. Every denominator of the chosen affine formula is a unit on each used residue flag. Work in the unramified field $\mathbb Q_{29}(\sqrt2)$ with the specified residue of $\sqrt2$. The exact two-equation Jacobian determinant at the flag is nonzero in all 32 rows. Multivariate Hensel therefore gives one root in that residue disc (and it is algebraic, since $j_{48}$ is a finite map of curves and the source equation has finitely many $j$'s). By the ordinary canonical lift criterion, the source canonical lift has the same CM order at this prime, since the CM field splits at 29 and 29 does not divide the conductor ([Edixhoven, Proposition 3](https://arxiv.org/pdf/math/0502213)). Every prime-to-29 cyclic flag lifts uniquely through a given ordinary canonical elliptic scheme. Hence the analytic characteristic-zero CM point with the stipulated source and exact ordered level is this unique Hensel branch. In particular the algebraic specification defines the original fixed point, not merely an arbitrary root in the same unmarked isogeny class.

All exact Jacobians and both coordinates are reported modulo $29^6=594823321$ in the fixed basis $1,\sqrt2$. The exact target equation $H_{f_{A/C}}(j_{48}(w_{48}(P_q)))=0$ and both source equations are replayed digit by digit. The p-adic digits are a reproducible check and root selector, not an approximation substituted for the defining equations. The characteristic-zero field of moduli over $K_*$ is the ring class field of the least common multiple of the two endpoint conductors ([Clark, Lemma 6.1](https://arxiv.org/pdf/2212.13316)); this describes how to join the named coefficient embeddings in later fixed arithmetic.

## 3. Handoff and remaining exact input

Every horizontal calibration divisor can now be specified algebraically as the actual zero divisors of the fixed $\mathcal G(P_q,\cdot),\mathcal H(P_q,\cdot)$ at these explicitly named roots with their Atkin transports and fixed signed occurrences. In particular the functions have the same fixed CM field; the zero branches are no longer represented only by a finite phase table. To use the fixed local maximal-order saturation one still needs the algebraic elliptic models of the divisor points and their distinguished 241-dual quotient flags, then the fixed compatible isogenies and tame torsion data. This note does not generate those larger tables, or supply the moving $D$. It does not turn an actual intersection support bound into an evaluated sparse valuation vector.

Replay from the preserved source layout using Python 3 and SymPy:

```sh
sha256sum -c SHA256SUMS
python3 -B check_fixed_K5_calibration_lifts.py | cmp - EXACT-KMINUS5-CALIBRATION-LIFTS.json
```
