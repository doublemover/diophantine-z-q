# Actual strict-Henselian even-contact roots

Strict kernel replay passes seven public theorems and all ten declarations in one module. Only propext, Classical.choice and Quot.sound occur.

The packet uses Mathlib's actual HenselianLocalRing property, actual local residue field, separable closedness, and actual canonical DVR additive valuation. It does not assume a square-root lifting conclusion or supply a unit/uniformizer decomposition.

1. An actual residue square root of a unit lifts to a square root in the ring. The polynomial is X²−u; its monicity, residue root and unit derivative are derived.
2. A separably closed residue field of characteristic different from2 supplies the residue root, hence every unit is a square.
3. Every actual even-contact expression u*pi^(2k) has a root, including k=0.
4. A finite even value of the actual canonical DVR additive valuation gives a root. The DVR unit/uniformizer decomposition is obtained from Mathlib, not passed as an input.
5. The exact square criterion includes the zero branch: x is a square iff x=0 or its canonical valuation is a finite even natural number.
6. The normalized unit equation has a simple root:2a is a unit.
7. Every root in every field receiving the ring is one of the two mapped ring roots. Thus the result covers all points of the local quadratic fiber, not merely one chosen root.

## Exact source application

The source tame local quotient is w=z². Over the actual strict-Henselian unramified DVR away from2, a contact of order2k is an actual integral square by square_root_of_even_valuation. every_root_of_even_contact then proves all roots already belong to that ring's image. The same statement applies in the reciprocal coordinate at infinity.

Construction of the strict henselization/unramified local extension, identification of the actual completed local curve quotient with w=z², and descent of finite fiber coordinates into a finite unramified extension are still geometric/local-field realization inputs. This packet does not silently infer those objects from its Henselian typeclass. It supplies the exact algebraic root and all-root assertions once those objects are realized. The source fine-level finite-etale lift is separate.

## Replay and dependency

Run bash build.sh. The exact official Mathlib Henselian source was not present in the binary cache, so it was compiled locally with debug.skipKernelTC=false; the script reproduces this if the compiled dependency is missing. Its source is unchanged and hashed in the receipt. The remaining official dependencies were obtained through the Mathlib cache. The module's recursive axiom audit includes all its used dependency proofs. No repository/Git operation was performed.
