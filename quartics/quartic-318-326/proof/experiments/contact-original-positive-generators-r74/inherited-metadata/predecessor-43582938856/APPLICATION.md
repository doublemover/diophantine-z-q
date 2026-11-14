# OriginalLineMayerVietorisQuotient318: expose the original quotient equivalence

## Observed scope and exact repair

Run43578868567 at977040de03da47698b89a3345d93e2ffcbc2220c, own positive-r72 artifact14107847364, verifies SectionLifting (6.381s), OpenSectionLifting (2.521s) and LineAffineOpenHOne (5.980s). First failure is the exported equivalence_mk rfl proof in OriginalLineMayerVietorisQuotient318 (30.496s): its defining equivalence is not exposed. The sole change adds @[expose] to that local equivalence definition, making its unchanged body available to exported definitional reduction. No boundary/difference or other declaration is exposed, no option is changed, and no proof body or theorem statement is modified.

## Required inputs and exact constructed object

The quotient is the original full overlap section group Γ(L.object,U⊓V) modulo the range of the original restriction difference. The difference still subtracts the actual presheaf restriction from V from the actual restriction from U, using precisely inf_le_right and inf_le_left. Its target remains the unchanged global derived H1 of additive L. The actual boundary is the original Mayer-Vietoris sectionBoundary, not a generic or newly manufactured map.

The equivalence remains the SAME composition: quotientAddEquivOfEq along (kernel_eq_range L U V h).symm, followed by quotientKerEquivOfSurjective for boundary L U V h and its original boundary_surjective proof. The first equality direction is range-to-kernel, and the second map on a representative is exactly boundary. The original full kernel-range equality and both actual affine-open acyclicity inputs supply every required hypothesis. Pinned Mathlib4 v4.35.0 QuotientGroup/Basic has an exposed public section; its quotient equality map, kerLift and right-inverse/surjective equivalence definitions retain these exact representative formulas. Only the local missing exposure is added.

## Quantifiers, scalars and consuming passage

Every original integral Scheme X, original line L, affine opens U,V covering X, and every original overlap section x remain quantified. There is no restriction to generators, rational coefficients, a generic point, nonempty opens, a trivial line or a proper overlap subobject. All additive carriers, scalar-forgetting maps, quotient subgroups and orientation signs are identical. No new existence or nonzero hypothesis is introduced, and no resource limit increases.

The immediate consumer of the changed definition is this same module's equivalence_mk, which evaluates the equivalence on the original QuotientAddGroup.mk x and retains the identical rfl proof. A source scan of the107 current root modules found no external application of this specific equivalence or its representative lemma. Do not treat an importer as a caller. Actual downstream uses of the unchanged boundary are OriginalLineRationalCohomology318.boundaryLinear/boundary_scalar and ContactOriginalCohomologyCoordinates318.coordinateBoundary/boundary_surjective; these use the same original derived boundary and full-open sections, not this equivalence to manufacture scalar structure. Those primary passages are retained.

## Verification boundary

Before c33d3679250312f1af8b155091bb9da5b747e4f3c27ed3de35a04fa3fe438c70; candidate2edc8923863adc1dadf9de45e7491fc0402e8ce6fd4aadb512a0a11dccede686. The complete107-module closure/order and other106 sources remain byte-identical. Distinct source/application and propagation review plus hosted Lean remain required. No local Lean/Lake, kernel or recursive-axiom acceptance, full packet pass or full arithmetic theorem claim is made.
