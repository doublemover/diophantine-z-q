# Degree-two raw companion exclusions for the same archived scalar

This package contains the exact proofs and independent signed review. It uses the literal archived input $a=0$, with $h=473592745039516333133760$, $s-1=6^{15}3^{65536}J$ from the preserved archived fiber, $\beta=204618888056724185$, and the **same** $\delta=1-b/17$. It does not change the pole or its source indices.

The parity proof excludes a degree-two and odd-degree pair. The exact four-branch proof excludes bidegrees $(2,4)$ and $(4,2)$. The [published degree-$(2,2)$ proof](https://github.com/doublemover/diophantine-z-q/blob/f54a4b099ec10826b88931513f84f8b4f4be6318/research/quartic-318-326/original-a0-no-bidegree-22-raw-section/source/NO-BIDEGREE-22-RATIONAL-PARAMETRIZATION.md) is cited, not copied. Together, any raw rational parametrization of this same surface, with both coordinates nonconstant and one of degree two, must have the other of **even degree at least six**.

These are not pointwise nonexistence results. Isolated rational points, higher bidegrees and paths with different projection shapes are not decided. No proof about changing the translated source index is part of this package.

Portable checks (Python standard library plus the ordinary SHA-256 utility):

```sh
sha256sum -c SHA256SUMS
(cd author/parity && sha256sum -c SHA256SUMS)
(cd author/bidegree24 && sha256sum -c SHA256SUMS)
(cd cold && sha256sum -c SHA256SUMS)
python3 -B replay_portable.py
```
