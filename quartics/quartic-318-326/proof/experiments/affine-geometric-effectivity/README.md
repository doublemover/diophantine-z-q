# Geometric affine overlap data reconstructs the original line

This36-source draft packet combines the canonical affine comparison coherence
with actual geometric-to-module diagonal/triple transport and the existing
faithfully flat rank-one reconstruction. It keeps every original line object
and its original global-section module.

## End-to-end result

For commutative rings R and S with an R-algebra structure and faithfully flat
S over R, start with an original line L on Spec S and an actual sheaf morphism
between its two pullbacks on Spec(S tensor_R S). Require:

- the genuine sheaf diagonal equation, using the original pullback-composition,
  Spec equality-transport and identity comparisons to L;
- the genuine sheaf triple cocycle on Spec(S tensor_R (S tensor_R S)), using
  the actual three tensor ring maps and those canonical pullback comparisons.

`OriginalGeometricAffineLine318` constructs a line on Spec R and an actual
pullback isomorphism to the unchanged L. It also proves that the reconstructed
module coaction transports to the original candidate coaction, and that the
original geometric/coaction correspondence recovers the exact original overlap
morphism, not only its class.

The geometric equations are not assumed to hold after applying a module
correspondence. That compatibility is the principal new argument:

1. The retained five tilde-coherence sources derive the actual canonical
   comparison's composition and identity laws from its original adjunction mate.
2. `OriginalLineComparisonComposition318` and `OriginalLineComparisonIdentity318`
   prove exact composition, morphism naturality and identity for the existing
   original-line sheaf and section comparisons. `OriginalLineNamedComparison318`
   retains equality transport at every named endpoint.
3. `OriginalGeometricEdge318` proves that an actual canonically normalized
   pulled-back sheaf edge maps to the corresponding original scalar edge.
   `OriginalGeometricTriple318` transports the actual geometric cocycle.
4. `OriginalGeometricDiagonal318` transports the actual geometric diagonal to
   scalar split-pullback comparisons. `AffineSplitDiagonalTranspose318` computes
   their genuine adjunction transposes, obtaining exactly the original module
   evaluation equation required for the counit.
5. The retained module cocycle-to-coassociativity and rank-one reconstruction
   now consume these proved geometric consequences, rather than new premises.

## Exact remaining boundary

The affine tensor-spectra nerve and its canonical sheaf maps are explicit. This
packet does not identify them with a separately constructed general scheme
fiber-product nerve, nor instantiate Mathlib's general geometric descent
category. The stated recovery of the overlap uses the established original
geometric/coaction equivalence. Identifying the displayed pullback isomorphism
itself with a morphism of the general geometric descent data is separate.

Non-affine cover compatibility and gluing, rigidification gluing, relative
Picard associated-sheaf identification, degree zero and Jacobian
representability remain further work. No unconditional arithmetic theorem is
claimed.

## Validation and provenance

Ten new sources are added to26 byte-identical producer copies. The copied
scalar-composition source is the explicit proof-elaboration repair from
`affine-overlap-coassociativity-r2`, not the failed original bytes. Other
producer copies come from that19-source packet, the five-source
`affine-tilde-coherence` packet, and the original sheaf-basechange packet.
Exact locations and hashes are retained in DEPENDENCIES.json.

Static hash/import/placeholder checks and audit-history self-tests pass. No
local Lean compilation ran, as instructed. All36 sources must undergo hosted
strict compilation and recursive axiom audit; independent acceptance is also
pending. Neither copied draft sources nor source-level review count as an
accepted-baseline result.
