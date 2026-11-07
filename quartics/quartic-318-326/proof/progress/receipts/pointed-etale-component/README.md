# Point-preserving quotient and proper arithmetic model

This packet closes the previously explicit point/component compatibility step and binds the invariant quotient to the actual proper-model pipeline. It does not construct the source relative torsion scheme or identify the result with the specified PEL curve.

## Constructed objects and maps

- `PointedComponent318.exists_component_through` starts with a finite-etale algebra over an integrally closed domain and an actual field-valued point. It derives the generic product decomposition, descends the primitive idempotents, and selects a domain component on which that same point evaluates to one. No domain, component or nontriviality premise for the cover is supplied.
- `ComponentPointFactor318` constructs the point's unique ring-map factor through the actual idempotent localization and proves equality of the corresponding actual Scheme maps. `PointedOpenJ318` specializes the existence theorem to the literal nonzero-level open-j ring.
- `PointedArithmeticModel318.ofPoint` constructs the component data. Its inclusion is open and closed in the original cover. Its actual source embeds openly in its normalization over the genuine projective j-line. The point is composed into that normalization, with exact compatibility over Spec Z. The very same scheme is integral, Noetherian and normal at every actual stalk, and is proper, flat and surjective over Spec Z. Its two actual affine chart rings have dimension two; its actual generic stalk is the generic tensor field of the same selected component, preserving coefficients.
- `PointedQuotientModel318` derives finite-etaleness of the actual invariant algebra from an actual equivariant faithfully flat splitting. It restricts the original-cover point to that algebra, constructs the component through this quotient image, and feeds it into the point-preserving model. Neither quotient finite-etaleness nor a domain component is an additional premise.
- `PrimitivePointedModel318` specializes to the existing `PrimitiveTorsion318.Primitive` residue pairs and the actual diamond subgroup action. The canonical primitive torsor formula and the pointed proper arithmetic model use the same original algebra, action and splitting. The canonical map is explicitly b tensor c maps to (g maps to b times rho_g(c)). Freeness is proved by the predecessor primitive-diamond packet, not assumed.

## Exact remaining source boundary

For the primitive specialization, the inputs still include the original algebra B, a faithfully flat splitting ring S, and an equivariant isomorphism from S tensor B to the function algebra on the actual primitive residue pairs. This packet does not construct the relative primitive N-torsion scheme of the source elliptic scheme or prove that its geometric fibers yield that splitting. A field-valued original-cover point is supplied; identification with a specified modular or PEL moduli point is not inferred.

The PEL/Shimura source, its canonical model and universal abelian surface, identification with this auxiliary modular construction, regular/semistable resolution, controlled-field/good-reduction data, maximal Hodge and Kodaira-Spencer identifications, and global Arakelov realization remain separate. No unconditional `RefinedGeometricRealization`, `FiveContact49Height`, or final Diophantine characterization is asserted. Normality and affine dimension two are not regularity or semistability.

## Replay and provenance

Run `bash build.sh`. All five source modules are rebuilt with `debug.skipKernelTC=false`, and every introduced declaration is recursively audited for axiom roots. Only `propext`, `Classical.choice` and `Quot.sound` are accepted. Imported dependencies use the pinned checked cache; this is not a fresh replay of the entire Mathlib/dependency closure. The receipt binds the exact sources, replay output and predecessor receipts. This is author-checked continuation, not an independent review or manuscript incorporation.

Frozen files are precisely the receipt whitelist plus receipt and SHA256SUMS. Diagnostic files and compiled artifacts are excluded. No repository, manuscript, shared branch or PR was changed.
