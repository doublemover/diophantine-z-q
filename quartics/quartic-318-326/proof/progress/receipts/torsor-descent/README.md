# Descent of the actual canonical torsor map

The packet proves faithful-flat descent of the actual action-defined tensor map, not just equality of ranks or existence of an unidentified algebra isomorphism.

For a commutative A-algebra B and an actual family of A-algebra automorphisms rho_g, the canonical map is

    B tensor_A B -> (G -> B),
    b tensor c -> (g -> b*rho_g(c)).

For a finite group G, an actual faithfully flat A-algebra S, and a genuine equivariant regular splitting

    S tensor_A B = (G -> S),
    e(rho_g(b))(h) = e(b)(g*h),

`canonical_bijective_of_faithfullyFlat_split` proves that this exact canonical map is bijective. `torsorEquiv_of_faithfullyFlat_split` packages it as an actual algebra equivalence, and `descended_tmul` retains the exact action formula.

## Proof content

- `regularEquiv` constructs the actual regular-cover tensor algebra isomorphism by finite tensor/product compatibility and the group pair bijection (g,h) -> (gh,h).
- `splitEquiv_eq_canonical` uses the actual equivariance equations to identify the constructed split isomorphism with the canonical map.
- `doubleBaseEquiv` explicitly identifies S tensor_A (B tensor_A B) with (S tensor_A B) tensor_S (S tensor_A B), using actual tensor associativity and cancellation of base change.
- `canonical_baseChange` proves the exact commutative diagram for this map and the actual tensor/finite-product identification on its target.
- Faithful-flat reflection of bijectivity then proves the original canonical map is an isomorphism.

No etaleness, normality, invertibility of |G|, domain assumption, torsor-law premise, or supplied canonical-map isomorphism is required.

## Source binding still separate

The theorem takes a regular equivariant splitting over the base A of the torsor. To apply it to the primitive-marking quotient, A must be the actual invariant algebra B^H. The preceding free-orbit packet constructs the regular split model over the actual invariant function ring. Transporting that regular splitting through the earlier original-base splitting and invariant base-change equivalence is a remaining concrete tensor/coordinate binding. This packet does not silently identify the original open-j base with the invariant quotient base.

The actual primitive torsion scheme, its splitting and free diamond action remain geometric realization inputs. This is not an unconditional proof of RefinedGeometricRealization or FiveContact49Height.

Run `bash build.sh` for a fresh strict-kernel rebuild and exhaustive recursive axiom audit of the one new module. Imported pinned cache dependencies are reused. No repository or Git edits were made.
