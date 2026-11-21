# Fixed final prime 103 and the even factor of a fixed-base detector trace

The same original linear-q source can protect 103 and use it as the fixed shared final Selmer prime. A pair of exact graph constructions retains both marked Selmer eights. On the first arm it also makes the even auxiliary factor have a nondegenerate two-dimensional pure Cassels pairing. This gives algebraic rank zero and its exact 2-primary Tate–Shafarevich group without a rank converse.

The analytic deduction for that **even** factor separately invokes Burungale–Tian, Theorem A of arXiv:2611.11566v1. With this input the first odd target is an exact fixed-base weighted ring-class problem over the quadratic field of discriminant −1751. It still needs the actual nonzero weighted phase. No odd target rank, companion even factor, numerical original source, or marked rational point is asserted.

```sh
(cd ct-original-fixed-final103-paired-selector-r1
 python3 check_fixed_final103_graph.py | cmp - EXACT-FIXED-FINAL103-GRAPH.json)
sha256sum -c SHA256SUMS
```
