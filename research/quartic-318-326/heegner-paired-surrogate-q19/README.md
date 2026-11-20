# One exact paired Heegner hit modulo 13

At the explicit surrogate scalar `b=(408/62269)^2`, the two prescribed squareclasses are 17 and 409. The **same** auxiliary field Q(√−455) and **same** prime 19 give the two literal twists 323 and 132107. The four fixed-weight theta coefficients give squared raw period residues 4 and 9 modulo 13. This yields rational nontorsion on both curves and, with the independent full Selmer checks, rational realizations of the same marked class. No point coordinates are claimed here for the new curve.

This is a substitute scalar, **not** an evaluation of the production scalar determined by (h,J), its candidate prime 1199923, or any linked production pole. It establishes neither prime density nor a uniform rank theorem. The companion residue is computed via the reviewed fixed-field calibration, not by direct replay of its full Heegner orbit.

- [Exact paper, bases and finite output](EXACT-SYNTHETIC-PAIRED-HEEGNER-HIT-Q19.md)
- [Independent cold review](independent-review/INDEPENDENT-PAIRED-SURROGATE-Q19-REVIEW.md)
- [Fixed-field calibration](../heegner-odd2544-theta/README.md) and [shorter exact-weight drivers](../heegner-odd2544-shorter/README.md)

## Replay

Requires standard-library Python 3.10+, GNU sha256sum, and a C++17 compiler. From this folder:

```sh
sha256sum -c SHA256SUMS
bash replay.sh
```

The replay verifies the frozen source dependencies in the two sibling dossiers, rebuilds the bounded exact enumerator and byte-compares all four coefficient entries. It also runs both the original and independent local arithmetic. For an isolated checkout, point `SHORT` to the shorter dossier and `BOOK` to the original dossier's `odd2544-weight-primefree-r1` subdirectory. The full input norm reaches 2,103,803,975; this exact bounded replay is not a new large-discriminant algorithm.
