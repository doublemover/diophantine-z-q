# Stable metric on the original modular Jacobian, without period matrices

[The proof](ACTUAL-ABEL-SUM-METRIC.md) computes the stable metric on the same ordered invariant wedge used in the original height comparison. The actual Abel sum from the product of the compact curve to its Jacobian has generic degree g!. That degree cancels the g! in the product integral of the alternating determinant. The result is the Gaudron–Rémond squared norm π^(-g) det(G) for the original conjugate-first Petersson Gram G. No symplectic basis or period matrices are needed by this proof.

The [original one-lattice witness](../original-one-lattice-geometric-witness/README.md) still supplies the finite contribution, with unchanged coefficient field, selected point over J=1, integral Hodge lattice and generic Abel–Jacobi pullback. The modular Jacobian J_X is not the arithmetic surface A. The statement uses the Gaudron–Rémond height convention; the original Faltings convention subtracts (g/2) log π.

The symbolic control checks the orientation sign, conjugate-first ordering, and factorial on exact finite-measure examples. It does not replace the cited proof on the compact Jacobian. Replay with Python 3 and SymPy 1.14.0:

```sh
sha256sum -c SHA256SUMS
python check-abel-sum-gram.py
```

This packet contains the independently reviewed paper and control, not a Lean implementation of the Abel sum, manifold integration, or height endpoint.
