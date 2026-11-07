# Actual five-contact coordinates

Strict-kernel PASS: one module, seven public theorems, twenty-one exhaustively audited declarations. Only propext, Classical.choice and Quot.sound occur in the audited closure.

`coordinates_of_original_models` proves the unique normalized labeled contacts lambda=2401 and mu=-343/32 directly from the four actual published quartic j-invariants. It first derives the six cross-ratio possibilities from an exact degree-six factorization of equality of Legendre invariants, then eliminates all thirty-six pairs using the other two labeled invariants. No precomputed candidate-list or numerical equality premise is supplied. The quartic denominators are separately proved nonzero, and `literal_contacts_match` checks the resulting tuple against all four rows.

The four rows are Gonzalez–Rotger, Journal of the Mathematical Society of Japan 58 (2006), Theorem 4.2 and Table 2, as pinned and independently checked in ../fiber-field-bridge/FIBER-PRODUCER.md and SOURCE-REVIEW.md. The original quartic-to-j formula is represented by `quarticJ`; the classical identification of that invariant with the Jacobian j, the labeled four-subset geometry, and the actual Shimura quotient construction remain named geometric theorem applications. This packet does not construct these curves or prove FiveContact49Height.

This strengthens, without changing the frozen hashes of, the exact-rational Python calculation in fiber-field-bridge. Replay with `bash build.sh`; build.log records the exhaustive audit. No repository or Git changes were made.
