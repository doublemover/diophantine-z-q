# Actual quotient traces on genuine sheaf cohomology

This packet supplies a concrete cohomology prerequisite for the eventual
Picard-tangent/Serre-duality comparison. It does not define H1 to be a dual
of the already known differential space.

## Exact proved maps

For each of the four original complementary completed quotient morphisms
and the original fifth completed quotient morphism f:C->E, the **actual**
structure-sheaf pullback O_E -> f_*O_C admits an actual sheaf retraction:
original regular-function trace divided by eight. The scalar 1/8 comes from
the original target structure map to Spec Q. The maps and equality hold on
every target open, including empty opens; no branch or infinity chart is
removed.

The ordinary additive structure sheaves are genuine sheaves on the small
Zariski sites of opens. `StructureAdditiveSheaf318.pushed_eq` identifies the
coefficient sheaf literally with the ordinary topological direct image.
`SheafCohomologyRetraction318` uses Mathlib's `Sheaf.H`, defined by Ext from
the constant integral sheaf, with the existing Grothendieck-abelian and
HasExt instances. There is no assumed duality, dimension, represented Picard
space or additional cohomology hypothesis in the actual consumer.

Applying this genuine cohomology functor gives, for every n >= 0,

    H^n(E,O_E) -> H^n(E,f_*O_C) -> H^n(E,O_E),

whose composite is identity. For all five original maps the first map is
therefore split-injective and the normalized transfer is surjective in
degree one. The associated cohomology projection is idempotent. These are
maps of abelian groups; this packet does not separately package a rational
module structure on H1.

Degree-zero comparison is explicit: the cohomology map is the original
pullback of actual global regular functions, and the transfer is exactly
the actual sheaf component. No normalization factor is dropped.

## Source modules

1. `StructureAdditiveSheaf318`: actual additive structure sheaves, their
   actual direct images, and the original structure-sheaf pullback.
2. `NormalizedStructureTrace318`: scalar restriction compatibility,
   division by the exact degree eight, and a genuine all-open sheaf retraction.
3. `ActualQuotientSheafRetraction318`: original all-open traces and exact
   retractions for the four complementary maps and the fifth map.
4. `SheafCohomologyRetraction318`: genuine derived sheaf cohomology,
   functorial retraction, injectivity/surjectivity, idempotence, and degree-zero
   normalization.
5. `ActualQuotientHOne318`: all-degree retractions and the explicit five H1
   injection/surjection endpoints.

## What remains separate

The codomain is **H^n(E,f_*O_C)**. It is not renamed or silently identified
with H^n(C,O_C). An actual direct-image cohomology comparison is a further
step. In particular this packet does not claim that the five H1 images form
a decomposition of one common source cohomology space.

The inspected pinned sources contain general sheaf cohomology, cohomology
maps, Cech complexes and Mayer-Vietoris, and the repository already contains
all-open trace maps. The bounded search did not locate a curve Serre-duality
pairing or a Picard infinitesimal-tangent identification. Building those
comparisons, with their variance and trace compatibility, remains separate.
The differential direct-sum equivalence belongs on the cotangent side of a
future Jacobian norm map; it is not identified here with the tangent of the
oppositely directed Picard pullbacks.

No degree-zero Picard component, representation, Jacobian, polarization,
isogeny, height theorem or all-integer witness theorem is claimed.

## Validation

The final fresh strict replay passes all five sources, including the H0
comparison; the private-inclusive recursive audit passes all54 declarations
with only propext, Classical.choice and Quot.sound. Repository audit-history
self-tests also pass; that check is structural, not mathematical acceptance.

See `receipt.json` for exact status and hashes. `check.sh` strictly
compiles all five source modules with pinned Lean4.35.0 and kernel checking
enabled, then recursively checks every module declaration, including private
and generated declarations, for only standard axiom roots. The baseline is
source/dependency-verified reuse, not a fresh complete source rebuild.

Three newly required official Mathlib cache targets and their dependencies
were acquired at the unchanged pinned revision. No compiler or dependency
revision was changed. `validate-source-policy.py` uses the existing repository
source policy against a temporary reconstruction of the exact original
1,837-module baseline metadata; it does not change a shared manifest.

Independent source acceptance and coordinated branch/hosted admission have
their own records and are not implied by producer validation.
