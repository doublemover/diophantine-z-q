# Actual quotient cover and split free-action torsor

Fresh strict-kernel replay passes all 38 declarations in two modules. Only propext, Classical.choice and Quot.sound occur. The earlier four-module etale-orbit-quotient packet remains unchanged.

## Actual quotient cover

`EtaleQuotientCover318.quotient_faithfullyFlat` derives that the actual inclusion B^G -> B is faithfully flat, from the genuine equivariant faithfully flat splitting used in the preceding packet. Its proof uses the derived finiteness and etaleness, the actual injection of the fixed subalgebra, and lying over. No domain assumption or supplied surjectivity is needed.

`quotient_cover` proves that the actual map Spec(B) -> Spec(B^G) is a surjective finite-etale cover. `quotient_topological` proves that its underlying continuous map is a quotient map. These are actual Mathlib schemes and morphisms.

## Full split free-action algebra

For a free group action on X, `FreeOrbitAlgebra318.coords` constructs an actual equivariant parametrization by G times the orbit set using representatives. `coverEquiv` gives an algebra isomorphism

    (X -> R) = (G -> fixedFunctions R G X)

over the actual invariant ring. The representative choice is harmless and used only to construct the isomorphism. `coverBasis` supplies the actual group-indexed invariant-ring basis. Under the stated nontriviality assumptions `cover_finrank` proves that the exact local cover degree is card(G).

`torsorEquiv` proves the full actual split torsor algebra identity

    B tensor_{B^G} B = (G -> B), with B = (X -> R).

`torsorEquiv_tmul` binds it to the genuine canonical action formula

    b tensor c maps to (g -> (x -> b(x)*c(g*x))).

This is not an arbitrary isomorphism between modules of the same rank. Its construction uses the actual free-action orbit coordinates, finite product/tensor compatibility and the pair bijection (g,h) -> (gh,h). No division by the group order is used.

## Exact boundary

Surjectivity and faithful flatness of the globally constructed quotient are proved. The canonical torsor identity in this packet is the split identity. Descending that exact canonical tensor map to an arbitrary equivariantly split algebra remains separate; it is not asserted by this packet. Likewise, the actual primitive elliptic torsion scheme, its splitting and the free diamond action remain geometric realization inputs. No unconditional RefinedGeometricRealization or FiveContact49Height is claimed.

Run `bash build.sh` to rebuild both modules with strict kernel checking and exhaustively audit their declarations. Imported dependencies use the pinned shared cache. No repository or Git edits were made.
