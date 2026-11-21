# The literal final anchor rules out small common-clearance label retuning

This theorem is about the exact original chart, all three original detector scales, and the actual row-287 anchor at \(S=3^{65536}\). It does **not** impose the archived \(a=0\) Lucas labels. It applies to every integer input \(a\) using this source and to arbitrary nonzero integer labels \(n_0,\dots,n_3\) with \(s=n_1\ne1\), **if the literal final anchor exists**. This hypothesis is automatic for the final original source completion using these labels, but is not required by the earlier three-detector or four-Ready preparation. No general obstruction to smaller intermediate Ready rows or to another source proof is claimed.

## 1. The anchor itself forces all labels odd

In the original notation \(z_n=-1/U(nR)\), \(Z=\prod_jz_{n_j}\), and \(c_2=N Z\). The literal normalized anchor ratio is
\[
    r=4096N Z+\operatorname{inverseNorm}(s)/S ,
\]
and the anchor implies that \(3r^2-2\) is represented over \(\mathbf Q\) by
\[
                        Q(X,Y,Z_0)=X^2+6Y^2-2Z_0^2 .
\]
This follows by dividing all three coordinates of the physical anchor by \(S\), without any point-pair or Selmer input.

Put \(a_2=\sum_j v_2(n_j)\). The exact original norm identities \(\operatorname{v}_2(N(U(nR)))=3+2v_2(n)\) and \(\operatorname{v}_2(\operatorname{inverseNorm}(s))=3+2v_2(s-1)\) apply to every admissible nonzero index. They give \(v_2(4096NZ)=-2a_2\), and the other summand has strictly positive valuation. Thus \(v_2(r)=-2a_2\) exactly. If \(a_2>0\), the normalized right hand side \(3r^2-2\) has an **even** valuation and its stripped \(2\)-adic unit is \(3\bmod8\).

The ternary form cannot represent such a value over \(\mathbf Q_2\). Strip a common 2-power from a nonzero triple and assume integer coordinates, not all even; this changes the output valuation by an even integer and keeps its stripped unit. If \(X\) is odd, \(Q\) is odd of residue \(1,5,7\bmod8\). If \(X\) is even and exactly one of \(Y,Z_0\) is odd the valuation is 1. If both are odd, \(6Y^2-2Z_0^2\equiv4\) or \(20\bmod32\), so \(X\equiv2\bmod4\) gives exact depth 3, whereas \(X\equiv0\bmod4\) gives exact depth 2 with stripped unit \(1\) or \(5\bmod8\). This exhausts integral primitive triples. Therefore \(a_2=0\): **all four labels are odd**, independently of how they were chosen.

## 2. The 3-adic constraint on the scalar index is necessary

The form cannot represent a rational with odd \(3\)-adic valuation and square stripped unit: \(X^2-2Z_0^2\) is a norm from the unramified quadratic extension at 3, so has even valuation (or is zero), while \(6Y^2\) has odd valuation with stripped unit \(2\) (or is zero). A finite sum of the two different parities cannot cancel; an odd-depth sum inherits the nonsquare unit from the latter term.

If \(v_3(r)<0\), the right hand side \(3r^2-2\) has odd valuation and square stripped unit. Hence \(v_3(r)\ge0\), allowing \(r=0\). As the labels are all odd, the exact original norm gives \(v_3(N Z)=0\). Also \(\operatorname{inverseNorm}(s)\) has depth \(2+2v_3(s-1)\), since \(s-1\) is even. If the scalar summand of \(r\) had negative depth, the unit \(4096NZ\) could not cancel it. Thus
\[
          2+2v_3(s-1)\ge65536,\qquad
          v_3(s-1)\ge32767,\qquad |s|\ge3^{32767}-1 .
\]
This necessity holds for exact rational anchors and even for their simultaneous local solubility at 2 and 3. The argument does not assert that the local conditions at these two primes alone produce the physical anchor.

## 3. No cancellation of heights in the literal product of odd labels

Use the original \(K=\mathbf Q(\sqrt2)\), \(E:y^2=x^3-D_E x\), \(D_E=(3-\sqrt2)^2\), \(R=(1+\sqrt2,2\sqrt2)\), \(P=2R\), and \(z_n^2=x(nP)\). The base-2 absolute logarithmic heights are exactly additive here:
\[
            h_2(Z)=\sum_j h_2(z_{n_j}) \quad
                   \text{for nonzero odd }n_j.
\]
Indeed it suffices to check the places of \(K\). At either real embedding \(|z_n|>1\) by the source quartic equation. At any non-dyadic good place, if some odd label gives a pole of \(z_n\), then \(nP\) reduces to the identity; the order of the reduction of \(P\) is odd. A zero of any other \(z_m\) at that place would force \(mP\) to reduce to the nontrivial two-torsion point \((0,0)\), contrary to that odd order. So all valuations at such a place have the same weak sign (if there is no pole, they are all nonnegative).

The only possible non-dyadic bad place is the arm of 7 with \(\sqrt2\equiv3\bmod7\). Here \(v(D_E)=2\) and the short model has discriminant valuation 6, hence is minimal. The reduction of \(R=(4,6)\) is nonsingular on \(y^2=x^3\), so \(R,P\) and all their multiples are in the subgroup reducing to the smooth locus. A positive valuation of the abscissa there would give the singular point \((0,0)\) (the equation also forces \(y\equiv0\)). It cannot occur. The other 7-arm is good. At the unique place over 2, the exact original \(v_2(N z_n)=-3\) for odd \(n\) makes every valuation negative, since the ramified quadratic completion has residue degree one. At every place, then, the positive parts defining the height of the product add exactly.

Apply the explicit \(\widehat h_2(P)>1\) and height error 5 from the separately verified duplication calculation. This gives
\[
          h_2(Z)\ge h_2(z_s)>s^2-5 .
\]
The relationship to sizes is literal: \(|c_1|,|c_2|>1\) because both real absolute values of \(Z\) exceed 2, and the local root bound on \(Z^2-2(c_1-c_2)Z+c_2\) yields \(h_2(Z)\le h_2(c_1)+h_2(c_2)+3\).

## 4. Consequence and actual remaining flexibility

Suppose the same labels are used for the original positive affine linear-\(q\) key, so \(t=u/(B^2q)\) and the three slope rows contain their **literal root \(-1\)** terms \(p_{j,-1}=u+(B/c_j)^2q\). Exact integral slopes force every \(B/c_j\) integral, so the reduced numerators of \(c_1,c_2\) divide \(B\), and their heights are at most \(\log_2 B\). Since \(c_0=1,\ u,q>0\), the slot-190 term satisfies the single strict bound
\[
 \boxed{\quad \log_2 p_{190,-1}>2\log_2 B>s^2-8
                   \ \ge\ (3^{32767}-1)^2-8.\quad}
\]
The last bound alone is greater than \(2^{103860}\), already in *bits*. This is an output/materialization bound under the exact common linear-\(q\) parametrization with the actual anchor. It does not depend on an arbitrary denominator-clearing presentation, the size of the Gaussian wheel, or on showing all labels simultaneously satisfy the Lucas relation. The numerical archived labels have an independent, much larger bound.

The source separation matters. The three-detector threshold and local-preparation theorems take nonzero labels and do **not** require the anchor. Even the four-pole Ready stage by itself does not use the physical ternary solution; a different low-height label tuple can in principle give a smaller arithmetic experiment there. But an exact PointPair or rank certificate on that experiment cannot be moved to a different high-depth tuple merely from its local agreement: the literal real scales, rational poles and companion squareclasses change. The final original consumer uses the same \(n_j\), the same \(N Z\) and the actual scalar \(\operatorname{inverseNorm}(s)\) for row 287. Thus changing the labels later does not meet its exact hypothesis. Decoupling the anchor would need a genuinely different original source construction or a theorem transporting the exact rational witness, not a smaller coefficient presentation of the same original chart.

This boundary is for the original chart-and-linear-key proof. It does not rule out another realization of the literal polynomial system, a symbolic number-theoretic proof at huge scale, a compact certificate for a giant integer, or an algorithm aggregating CM phases without explicitly materializing all prime factors.

## Exact source pins and replay

- `ScalarCompleteSource318.lean` a0f74e00bdd0be89dee1cac08d935908bb225610dba88d9564d9c99916a03323 (actual anchor and final consumer), `ActualAnchorRatio318.lean` 2f248c0f28f5a8349040950d3c22d1c756b7747ff90664fbb129484432bcc490 (normalization), and `Current318FinalPolynomial.lean` ad54e02ec0321113faba7c68751876badd2f8db1f4a39ad9a8f09e1da01a9bb1 (exact scale).
- `ScalarIndexValuations318.lean` 9cdb43f04b037d453a100c9eacca01eaabe874159005771c3e1481bf90ed21af, `FixedAnchorNormDepths318.lean` a3449c50052035645d2a14fa1f9691a8a7c32de071e707e547ca650d15fa82fa (2/3 identities); no alteration to these source files.
- [Explicit duplication calculation and archived-label bound](../original-linear-q-a0-archived-clearing-height-floor-r1/ARCHIVED-A0-COMMON-CLEARING-HEIGHT-FLOOR.md), SHA-256 410bb6ca0ef117af4b4389134e135af802bc000ea13f10064677819d1f6f7416.
- `ThreeDetectorCRTWitness318.lean` 837caa15e52f368f9a2e98443e4b410bd64884fbf7b456dd9053eab9fd6812d0, `SourceLocalProgression318.lean` cd5f09f0db78cbb46282e6557d97a2ab34b8047da449a41ad97ee124875f9b91, and `PreparedIntegerSource318.lean` e3ecec834054e138eb6cc64c92f0e431510c64a878803d689fa55a9fdf06c423 (same-input Ready versus final source dependency).

```
python3 -B verify_final_anchor_clearing.py | cmp - EXACT-FINAL-ANCHOR-CLEARING.json
sha256sum -c SHA256SUMS
```
