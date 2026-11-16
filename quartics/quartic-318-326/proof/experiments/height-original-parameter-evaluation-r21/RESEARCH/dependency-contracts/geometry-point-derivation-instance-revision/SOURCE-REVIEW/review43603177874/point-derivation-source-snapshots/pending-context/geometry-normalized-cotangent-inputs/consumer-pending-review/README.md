# Finite cotangent evaluation images and original-place frames

Inactive, source-review-pending research. No Lean run or kernel/hosted acceptance.

## Constructed, not assumed

For a finite integral module E and its supplied linear evaluation into the ORIGINAL point field, the embedded submodule is defined as the actual range. Native `Submodule.fg_range` proves its finite generation. A nonzero evaluated section then supplies the previously reviewed maximum-norm generator and free frame of exactly that range. The evaluation need not be injective, and E need not be torsion-free or rank one.

For an essentially finite type algebra A over the actual finite-place integer ring V, together with an integral point A→V compatible with V→A, the construction uses the genuine pullback `V tensor_A Omega(A/V)`, not `Omega(K/V)`. Native Kähler finiteness and tensor-base-change finiteness prove this module finite over V. Its tensor square is finite as well. A supplied V-linear cotangent coordinate functional is extended bilinearly to an actual quadratic evaluation; on pure tensors it is literally the product of the two original evaluations.

At every excluded original place, supplied lifts of BOTH unchanged a0 and a1 into that quadratic module construct the original `FiniteModels` input. Its lattice is exactly the quadratic-evaluation image, not a freely chosen abstract rank-one module. The downstream free frame, generator and original-section membership follow. Previously constructed good-place lattices remain fixed. Original a0's existing nonzero theorem excludes the zero image; no caller rank/free-frame/nonzero-module/image-FG assumption is added.

## Geometric prerequisites still required

The finite-type charts, integral point algebra structures and compatibility, cotangent evaluation functional and exact original section lifts remain inputs. This bundle does not construct the global regular/maximal model or prove that a normalized point-dependent chart is regular. It does not identify a singular model's cotangent square with a dualizing square, nor its evaluation image with the required maximal-model lattice. The coordinate functional has not yet been constructed from an actual geometric generic differential/derivation. These identifications cannot be replaced by finite generation.

Essential finite type is explicit and used by the native Kähler theorem. Finiteness does not follow here merely from normality, a finite point set, or the existence of a model. No Hodge metric, native KS map, archimedean bound, product-formula degree identity or per-point GeometricRealization is claimed. The separate native-q sign bridge remains a different conditional result.

## Exact source boundary

Four new sources depend on five exact source-reviewed map/frame files and the unchanged 173-module r16 closure. The planned 182-module order remains inactive behind CommonRestriction. Pinned native APIs are `KaehlerDifferential.finite`, `Module.Finite.base_change`, `Module.Finite.tensorProduct`, and **Submodule.fg_range** (not a theorem in the LinearMap namespace). All scalar rings are the original finite-place integer rings, not completions or differently normalized valuation rings.

The four-source source/contract review must check the actual native declarations, dependent scalar structures, original consumer identity and all excluded indices before this bundle can be described as source-reviewed. Static provenance checks are not Lean validation.
