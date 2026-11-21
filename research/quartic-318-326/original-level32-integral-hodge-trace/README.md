# A prescribed trace entry in the original modular Hodge lattice

The original compact curve and whole signed polynomial are unchanged. On the fixed number field, an explicit level-32 invariant differential multiplied by **2** gives a genuine nonzero row of the same integral Néron Hodge lattice of the modular Jacobian. The explicit integral multiplier gives one prescribed global trace entry **2^481 · degree(p)**. The whole column for the ring element 1 is zero.

- [The integral Hodge row and exact entry](ACTUAL-INTEGRAL-LEVEL32-HODGE-ROW.md) proves that no unspecified denominator is needed for this row.
- [The modular polynomial and original normalization](EXPLICIT-LEVEL32-ORIGINAL-TRACE-ENTRY.md) calculates the literal modular map and the integral multiplier.
- [The trace-zero column](ACTUAL-ORIGINAL-HODGE-TRACE-ENTRIES.md) is the accompanying earlier argument for all rows and the ring element 1. Its arbitrary row denominator is superseded only for the particular level-32 row in the first note.
- [The original one-lattice geometric witness](../original-one-lattice-geometric-witness/README.md) identifies the same geometric Hodge and trace data used by the height comparison.

The two signed review notes concern the paper statements and their separate symbolic controls. Test the controls with Python 3 and SymPy 1.14.0:

```sh
sha256sum -c SHA256SUMS
python check-level32-polynomial.py
python check-integral-row-algebra.py
```

The controls do not replace the cited geometric arguments. This is **one specified nonzero entry and one forced zero column, not a calculation of the complete matrix**. The modular Jacobian is not the arithmetic abelian surface A supplying the opposite height inequality. This package contains no Lean source, build result, registry change, or native Néron-model claim.
