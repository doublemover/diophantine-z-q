Exact Mathlib pin56a005855ea17e0b0958f73ec801ae140b0a1679.
GroupAction/Quotient.lean retains the actual orbit relation and self orbit
decomposition used by accepted FiveBranchCount318. That entire accepted
source has been read, including actual8-point orbit theorem, sigma count,
nonidentity incidence bijection and genus5 conditional endpoint.
Data/Fintype/Card.lean card_congr/card_le_of_injective act on exact finite
types, not arbitrary selected subsets. Equal finite cardinal plus injective
actual displayed map yields bijective via the same accepted FourRootGalois318
use of Fintype.bijective_iff_injective_and_card.
Actual producer sources read in full: PELOriginalFiniteBranchImage318,
PELMaximalFiberCardinality318, PELMaximalQuotientProper318,
PELStabilizerLocusInvariant318, PELOriginalLabeledFixedOrbits318,
PELOriginalBranchLabels318 and PELOriginalMaximalQuotient318.
Their exact frozen bytes are independently identified in COPY_BINDINGS.
projection_eq_iff x y means existsg,g•y=x; the displayed injection uses
that direction and reverses the resulting index equality. Full original
fixedLocus invariance uses actual commutative Labels action, not unnamed
bijections of fibers. The actual branch image is a subset of SAME maximal
quotient; original_locus_union and branch_image_iff identify SAME whole
ramification source. No algebraic/analytic comparison is assumed silently.
OrbitQuotientCurrent.lean: f1578f5d3d96929af2e7f4e0aa2da38b5acc3864dca2897196e0dacbc31ef05d
FintypeCardCurrent.lean: ba761ef9e5a76c2c2d36ed873a57072f858d824cf475a904de93db1c01ccdeba
Accepted FiveBranchCount318.lean: e2a933a475c039ca5a0b39c5d182b676002fdca7df8ea6731bf3111c3691c46d


## Exact finite-cell partition/count primary bodies

All fetched/read at pin56a005855ea17e0b0958f73ec801ae140b0a1679.
Algebra/BigOperators/Group/Finset/Piecewise.lean prod_dite is annotated
to_additive and thus supplies Finset.sum_dite for full finite-set dependent
partition. Data/Fintype/BigOperators.lean Fintype.prod_dite proof converts
its two filtered univ subtypes to the full p and notp subtypes. There is NO
Fintype.sum_dite declaration at this pin. The new sum_partition proves the
additive formula explicitly, copying that full-index argument rather than
using a nonexistent name. Logic/Equiv/Basic.lean subtypeEquivRight is the
original identity-on-points subtype equivalence with e:forallx,p x iff q x;
its forward/backward values retain the same x with transported proof.
Algebra/BigOperators/Group/Finset/Defs.lean Equiv.sum_comp is the to_additive
of Equiv.prod_comp and ranges over complete finite types, whereas the Perm
overload needs a Finset; the new helper uses the qualified Equiv name.
The same file proves full finite sums respect sums/constant values. Actual
Fintype.card_sigma sums all dependent fiber cards. Original sigmaFiberEquiv
is used with its literal original cell map, so no fiber is silently dropped.
Supplement to214 primary pins: Fintype/EquivFin.lean269 proves bijective iff
injective AND card(domain)=card(codomain), with both Fintype hypotheses.
GroupAction/Defs.lean477–493 defines actual selfEquivSigmaOrbits via literal
quotient fibers and original orbit equivalence. Exact bodies read, not just
re-exporting imports or previous usage.
FinsetPiecewiseCurrent.lean: 44ca810b534d34f4e75a884115f531e59ad068c4aa0209899e1053050018adef
FintypeBigCurrent.lean: 2f0d638d946feff577d4dde3f152c024b069d247ae7a4cf22fe1948ce9affd7e
EquivBasicCurrent.lean: f4c8ca35dcd91f868633d51b7c7c51b2dc05ca83193fa6519ab9f7ed41c360dc
FinsetEquivCurrent.lean: 710646cfc1c9a4b851ce57c336f072acb8aa1aeb8d4a1f4aca6551c96fee66f9
FintypeEquivFinCurrent.lean: 06b87a62327f755055be10f5db06d7bd105bf7e0413f98edea22aeee4db924fb
OrbitDefsCurrent.lean: 7f9f4f3768ee7e1403680aadea4599b34e5e88a8c8234fec1cc3bbd6dec138ee
