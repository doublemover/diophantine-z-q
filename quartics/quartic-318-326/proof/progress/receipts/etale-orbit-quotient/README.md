# Actual finite-etale invariant quotient

This packet constructs the actual fixed coordinate algebra and its affine spectrum. It does not assume a quotient algebra, an invariant/base-change isomorphism, or invertibility of the acting group's order.

## Checked construction

1. `OrbitAlgebra318.orbitEquiv` identifies the actual subalgebra of invariant functions on a finite set X with the function algebra on the actual orbit quotient X/G. The invariant algebra is consequently finite etale over every commutative base ring R, including characteristics dividing the group order.
2. `InvariantBaseChange318.baseChangeEquiv` proves that the actual invariant algebra of a finite family of algebra automorphisms commutes with flat scalar extension. All fixed equations are encoded in a single linear map B -> (G -> B). Tensor exactness and tensor/finite-product commutation prove surjectivity; flat preservation of injections proves injectivity. This is not averaging.
3. `EtaleInvariantQuotient318.finite_etale_of_faithfullyFlat_split` takes an actual faithfully flat R-algebra S and an actual equivariant algebra isomorphism S tensor B = (X -> S). It derives that B^G is finite etale over R. The original B is also finite etale over B^G, and every further base extension of B^G is finite etale. `existsUnique_factor` proves the actual affine quotient universal property for invariant coordinate maps.
4. `OrbitQuotientScheme318` defines the actual scheme Spec(B^G), its structure map to Spec(R), and the quotient map from Spec(B). Both maps are proved finite etale. Each supplied automorphism becomes trivial after the quotient map.

The automorphisms are indexed as a family because pullback reverses composition. Only the fixed equations matter. The equivariance equality explicitly binds their action to the actual action on X; it is not a hypothesis about an unidentified quotient.

## Exact source application and remaining boundary

For the open j-line use R = OpenJModel318.Base N, namely Z[j,1/(6N*j*(j-1728))]. Let B be the coordinate algebra of the actual primitive N-torsion scheme of that elliptic model, let G be the actual diamond subgroup H, and let S be a faithfully flat ring over which the torsion cover and the H action are split. Evaluation at the labelled torsion points gives the required equivariant algebra isomorphism. The output is the actual finite-etale affine H quotient, without inverting |H|. This closes the invariant/orbit and finite-etale descent portion of the source's integral open-j construction.

The packet does not construct the primitive N-torsion scheme, its finite-etale trivializing cover, or its identification with the point-level modular moduli problem. Those geometric antecedents remain explicit. It also does not assert that an affine universal property alone is the full scheme or fppf-sheaf quotient universal property. Identification with the modular normalization and the global Shimura/Hodge/Arakelov realization remain separate. In particular, RefinedGeometricRealization and FiveContact49Height are not asserted unconditionally.

## Replay

Run `bash build.sh`. All four modules are rebuilt with `-Ddebug.skipKernelTC=false`, and every declaration introduced by those modules is recursively audited for axioms. Only propext, Classical.choice and Quot.sound are permitted. Imported Mathlib dependencies use the pinned shared cache; this is not a full dependency-closure replay. No repository or Git edits were made.
