# The archived input-0 labels force a nonmaterializable common clearing

This is about the exact archived \(a=0\) Lucas label tuple and the original three-detector positive linear-\(q\) key. It supplies an **output bit-length floor for a single genuine prime of slot 190**, already before one imposes the Gaussian ray, primality, formal orders or a real threshold. It does not exclude different admissible labels or a proof by compact arithmetic certificates. It is not the earlier fixed-wheel floor.

## 1. Exact source and unavoidable row term

Write \(K=\mathbf Q(\sqrt2)\), \(D_E=11-6\sqrt2=(3-\sqrt2)^2\). In the source \(E:y^2=x^3-D_E x\), the actual half-generator is \(R=(1+\sqrt2,2\sqrt2)\) and \(P=2R\). Let \(z_n=-1/U(nR)\) be the literal fixed root. The homogeneous duplication chart gives
\[
 z_n^2=x(nP)
\]
for each nonzero label, not a square root chosen anew at specialization. For the four labels \(n_j\), set \(Z=\prod_j z_{n_j}\). The three literal **unsquared** scales are \(c_0=1,\ c_1=\Re Z+N Z,\ c_2=N Z\), where \(\Re\) means the half-trace and \(N\) the quadratic norm.

Let \(B=D_{\rm clear}Q>0\) be the common clearing multiplier in a numerical key, so \(t=u/(B^2q)\). In the published route \(D_{\rm clear}^2/c_j^2\) is already an integer for the root \(-1\) in every row. Even if one only asks for the exact integer linear slopes after multiplying by \(Q^2\), this root requires \((B/c_j)^2\in\mathbf Z\). A rational number with integral square is integral, so \(B/c_j\) is an integer. Consequently the reduced numerator of each \(c_j\) in absolute value divides \(B\). This condition is forced by the original \(-1\) root, not by the particular choice in the clearing lemma. Any reparametrization giving the same actual \(u,q,p_{j,-1}\) preserves that integer: \((p_{j,-1}-u)/q=(B/c_j)^2\). In particular the literal unscaled row 190 contains the unavoidable positive term
\[
                   p_{190,-1}=u+B^2q>B^2 .
\]
A local residue replacement for a label, a different chart, or a smaller auxiliary \(q\) does not change this identity for the archived rational scales.

## 2. An explicit global canonical-height comparison

Use logarithmic heights in base 2. The homogeneous degree-four duplication map in the abscissa is
\[
 F=(X^2+D_E Z^2)^2,\qquad
 G=4XZ(X^2-D_E Z^2).
\]
Its homogeneous resultant has absolute value \(2^{12}D_E^6\) up to sign; the simple evaluation is at the two repeated roots \(X^2=-D_E\) after \(Z=1\), with no lost common point at infinity. Its rational norm is \(2^{24}7^{12}\). At each finite place the model coefficients are integral. After normalizing at least one homogeneous coordinate to a unit, the resultant Bézout identities in that affine chart bound the absolute maximum of \(F,G\) below by \(|\operatorname{Res}(F,G)|\) and above by \(1\). Both coordinate choices use the same homogeneous resultant up to sign. At each real embedding \(2<D_E<20\), so the absolute maximum has lower bound \(\max(|X|,|Z|)^4\) from \(F\) and upper bound \(441\max(|X|,|Z|)^4\). Summing the local estimates yields the deliberately rounded uniform bound
\[
          |h_2(x(2Q))-4h_2(x(Q))|\le30
\]
on the projective formula (including the point at infinity), because \(12+6\log_2 7<30\) and \(\log_2 441<9\). Telescoping the canonical-height limit gives
\[
 \left|\tfrac12 h_2(x(nP))-n^2\widehat h_2(P)\right|\le5 .
\]

For the numerical positive lower bound on \(\widehat h_2(P)\), the actual chart gives
\[
   x(P)=57/8-(7/2)\sqrt2,\qquad
   x(2P)=8226963211/2285245536
                    -(1063929023/1713934152)\sqrt2.
\]
The primitive integral minimal equation of \(x(2P)\) has leading coefficient \(1974452143104>2^{40}\). It is obtained by clearing the rational primitive equation \(T^2-\operatorname{Tr}(x)T+N(x)=0\), with the nonzero irrational coefficient verifying degree two. The algebraic height formula gives \(h_2(x(2P))>20\). Therefore \(4\widehat h_2(P)>5\), in particular \(\widehat h_2(P)>1\). There is no use of an ineffective canonical-height lower bound.

## 3. Archived Lucas labels and the clearing floor

Use the exact positive archived \(J\), and \(i=6^{15}3^{65536}J,\ s=1+i,\ k=2(s-2)\). The actual labels are
\[
    3723,\quad s,\quad n_*=U_s(k+1),\quad U_s(k)/(s-2),
\]
where \(U_s(0)=0,U_s(1)=1,U_s(j+1)=sU_s(j)-U_s(j-1)\). The replay verifies the archived 864-bit \(J\), \(s\) of bit length 104775, and \(k>2^{104774}\). No huge Lucas value is materialized. Positivity and the recurrence give \(U_s(j+1)\ge(s-1)U_s(j)\) for \(j\ge1\). Thus \(n_*\ge(s-1)^k>2^k\), and each of the other three labels is at most \(n_*/4\). The elementary height triangle inequality on \(\prod z_{n_j}\), and \(h_2(z_n)=h_2(x(nP))/2\), now give
\[
    h_2(Z)\ge(n_*^2-\textstyle\sum_{n_j\ne n_*} n_j^2)\widehat h_2(P)-20
                  > 3n_*^2/4 .
\]
The two real absolute values of \(Z\) are each greater than \(2\): each \(U\) satisfies \(V^2=1-D_EU^4\), so \(|Z_\sigma|\ge(D_E)_\sigma>2\). For \(r=|Z_+|,s'=|Z_-|>2\), \(|c_2|=rs'>1\) and \(|c_1|\ge rs'-(r+s')/2>1\). Hence \(h_2(c_j)\le\log_2 B\) on both literal nontrivial scales. From \(Z^2-2(c_1-c_2)Z+c_2=0\), the elementary local root bound is \(M_v=\max(1,|2(c_1-c_2)|_v,|c_2|_v)\) at finite places and \(2M_v\) at real places. The triangle inequality on the coefficient vector gives
\[
             h_2(Z)\le h_2(c_1)+h_2(c_2)+3\le2\log_2 B+3.
\]
It follows that \(\log_2 B>n_*^2/3\). The same statement holds for \(D_{\rm clear}\) itself when its pre-\(Q\) slopes are already integral as in the published clearing.

In particular **even the one slot-190 prime** has binary logarithm
\[
       \log_2 p_{190,-1} > 2n_*^2/3 > 2^{2k-1}
                             > 2^{\,2^{104774}}.
\]
The statement bounds the size in *bits*, not just the prime's numeric magnitude. It is a lower bound for an explicit output or scan on these exact labels and this common-clearing construction. It says nothing about circuit primality certificates, a changed source proof, a different admissible label tuple, or the general complexity of the seventh-moment aggregate. The only executed work here is the exact bounded verification below; no prime search was started on the archived roster.

## Source pins

- Literal chart and fixed root: `CoherentMultipleCharts318.lean` SHA-256 01443a070ea295862a1c06111e8803651d6766afead3c3918797aa5718ba9bc9. Literal scales: `FixedDetectorScales318.lean` 0d34c0be7293797c04c6696e8921a2abb61fcf5cb4447da5d3dd995c2928e9ce and `ThreeDetectorUniformFamily318.lean` df9f80935c672c24ed8d095be490c4253951c69af224fbf8236d9d54737fe42b. Clearing `ClearedContactForms318.lean` 1ed66c70b966ecf2b036c3efbc92e87999a981f92602dd318fd0993cacac875d.
- [Published archived input-0 order-only check](https://github.com/doublemover/diophantine-z-q/blob/f767adfb/research/quartic-318-326/actual-linear-q-local-numerical-check/linear-q-literal-order-only-canary-r2/LITERAL-A0-ORDER-ONLY-Q-CHECK.md), SHA-256 e45cfbf487f36c8659697632c104e1c5f03b652e43e083a245ce9b236cc87a94. It supplies the literal Lucas labels and same scales, not a complete key. The pinned prefix JSON SHA-256 is 5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7.
- [Published original linear Gaussian key](https://github.com/doublemover/diophantine-z-q/blob/97adcaf7e8331759afbced0339d1a267ac8bf5c4/research/quartic-318-326/actual-linear-denominator-prime-route/original-linear-denominator-prime-route-r1/LINEAR-GAUSSIAN-PRIMES-TO-ORIGINAL-READY-POLES.md), SHA-256 29e5419420d73d1699801548e411527e265378ebd22bde95d7f7653d59fbc3e0.

```
python3 -B verify_archived_clearing_height_floor.py | cmp - EXACT-ARCHIVED-CLEARING-HEIGHT-FLOOR.json
sha256sum -c SHA256SUMS
```
