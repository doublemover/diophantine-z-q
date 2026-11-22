# A fixed t=18 first point on the literal original scalars at −1 and 617

This supplies only the first equation of `NormalizedPolePoints318.PointPair` at two actual original scalar inputs. It does not supply either companion, choose a new source index, compute any literal complement, or infer a rank or combined four-pole result.

## 1. The native scalar and its two square scalings

For each retained actual source put $R_s=\operatorname{inputR}(a)$, $K=1+114444R_s$, and let $W$ be its original packed value. The native `ScalarForwardWitness318.poleInput` and `PreparedIntegerSource318.scalarB` give
\[
 b=114444R_s(W/K)^2,\qquad B=17b=B_0(204W/K)^2,\qquad B_0=187R_s/4.
\]
In particular `scalarB` denotes the native $b$, not $B=17b$. The actual `scalar_domain` proof supplies $0<b<17$ in the two cited prepared source rows, so $B>0$ and $W/K\ne0$. None of the formulae below substitutes $W=1$ or switches to a graph control.

* At $a=-1$, `inputX=a+a²=0` as at $a=0$. On the **same** $h$ and translated label `labels 1`, `detector33` and `detector37` are independent of the input, and the inverse norm sees only `labels 1`. Thus $W,K,b$ coincide on such a same-index comparison. For the actual sharp $a=-1$ scalar use its own retained $h,s$, whose Ready proof and equality to input zero at that same pair are already pinned. In either case $R_s=4376874610839020$, $B_0=\beta_0=204618888056724185$, and $B=\beta_0\rho^2$ with $\rho=204W/K$. Equality of scalar values at *different* source pairs is neither assumed nor needed.
* At $a=617$, use the same materialized $h,J$ and original labels of the cited scalar JSON. It has $R_s=66540735456245258815946020283188225080332$, and
\[
 B_0=(11\cdot359)^2\beta_{617},\qquad
 \beta_{617}=199477972060937362209233596181078921.
\]
The exact same $K$ can also be written $1+2448B_0$. Therefore $B=\beta_{617}\rho^2$ with $\rho=204(11\cdot359)W/K$. The indexed chart certificate gives the required guard for the literal scalar. It is not a guarantee of the three other poles or the physical anchor.

## 2. One identity on each required fixed base, and exact original coordinates

Write \(\beta\) for the indicated positive representative and fix \(t=18\). Set
\[
 \nu=\beta t^2,\qquad A=1+3\nu,\qquad k=(1-\nu)(1-9\nu),\qquad n=\beta k.
\]
On the fixed base \(E_n:Y^2=X(X-n)(X+3n)\) take
\[
 P_{\beta}=(\beta A^2,\ 8\beta^2tA(1-3\nu)).
\]
Indeed \(X-n=(4\beta t)^2\) and \(X+3n=4\beta(1-3\nu)^2\), giving the exact ordinate identity and ordered class \(([X],[X-n])=([\beta],1)\). The marked point does not use \(W,h,s,J\). Thus at input \(-1\) the old input-zero numerical point itself is on the required fixed base, even when the actual scaling \(\rho/A\) differs. At input \(617\) it is the same explicit **identity** with a different \(\beta\), not reuse of the old coordinates: the representatives already have distinct squareclasses at 5 (old exponent 1, new unit). The two fixed parameters are in fact distinguishable at 13: the old \(n\) reduces to 80 modulo 169 and the new one to 13; the first curve has good reduction there and the second has an odd ramified twist of a good curve. This is not a statement about any other fixed graph model.

For each actual scalar, scale \((X,Y)\) by \(((\rho/A)^2,(\rho/A)^3)\) and put
\[
 T=n(\rho/A)^2=B k/A^2,\qquad
 y_1=8\beta^2t\rho^3(1-3\nu)/A^2.
\]
The scaled abscissa is exactly \(B\), and the ordinate gives the literal native first equality
\[
 y_1^2=B(B-T)(B+3T).
\]
Here \(\nu>1\), hence \(k>0\); and \(A^2-k=16\nu\) gives \(0<T<B\). The ordinate is nonzero. No computation of a complement or claim about its squareclass, no companion, and no rank certification is part of this transfer.

## Exact source bindings and replay

- Native `ScalarForwardWitness318.lean` `9b21f269bbf73da643a7259f71dc67ea835a52aaa97bbb6d449549004bf7038c`, `ScalarActualInputs318.lean` `669eb03d31c5490f7278608a416e1e44ec64d10aa90c044c64c6636759e810f1`, `PreparedIntegerSource318.lean` `e3ecec834054e138eb6cc64c92f0e431510c64a878803d689fa55a9fdf06c423`, `NormalizedPolePoints318.lean` `410995ba113f37dfcb54261e61eb6b90fde58242a4fa0eed79282e99ad060542`.
- Sharp input-minus-one proof `0449a6016288fd5427719413adc719a8c9ef6bc569a06666b484a9bc3da350a9`, list `7a3ff6e99c9d4873a41c067ab9ca97cc8a1e109b260107587b4e59eba640abd7`. The separately archived input-zero first point is [the published exact input-zero donor](https://github.com/doublemover/diophantine-z-q/tree/e6ab359e9915c0ab142145a2d26937e6d8e05a27/research/quartic-318-326/original-a0-t18-literal-trace-index), author `5dcb7aed94a3be91c5ecf2de57fba678ab00fe93741df876e80f7b6cbf6216e4`, list `16ba82294a3aeef50bfd7182c33ab01fa04a3e541238e2870be2901b3cdb312b`.
- Exact input-617 record `7f22536b2da38e57de106f7ea63c0ed10226144d78ec2ec09fdfbbb82d10d8af`, reconstructed scalar paper `882b8b12f7c41976ac38d1f0f541a2ac6cf43881fa2dfbf36c45648794dfe499`, list `0a59f95dc56fec541c99877690aa90807e3a75e40fc4b7dcee20ba0b376d3848`.

The fixed-integer replay checks the native input polynomial at 0, −1 and 617, the square factors, the point identities, the old numerical base and the indicated separation. It does not read or evaluate the packed scalar value.

```sh
sha256sum -c SHA256SUMS
python3 -B replay_two_input_first_points.py | cmp - EXACT-TWO-INPUT-FIRST-POINTS.json
```
