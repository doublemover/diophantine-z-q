module
public import ProperAffineSections318
public import HodgeInvertibilityCriterion318
public section
noncomputable section
namespace DomainHodgeComparison318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] (A B : R)

/-- Canonical structure-sheaf descent on the actual completed family over a
domain base, now supplied by properness, integrality, and its actual section. -/
@[expose] def structureIso :
    SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf ≅
      (Scheme.Modules.pushforward (WeierstrassGluing318.structureMap A B)).obj
        (GlobalInvariantLine318.line A B) := by
  letI := ProperAffineSections318.family_unitMap_isIso A B
  exact asIso (StructurePushforwardSplit318.unitMap (WeierstrassGluing318.structureMap A B))

/-- Evaluation of the previously glued invariant line is canonically invertible.
This statement concerns that actual line, not an unproved intrinsic Omega frame. -/
@[expose] def invariantLineEvaluationIso :
    (Scheme.Modules.pushforward (WeierstrassGluing318.structureMap A B)).obj
        (GlobalInvariantLine318.line A B) ≅
      (Scheme.Modules.pullback (WeierstrassGluing318.infinity A B)).obj
        (GlobalInvariantLine318.line A B) := by
  letI := ProperAffineSections318.family_unitMap_isIso A B
  letI := HodgeInvertibilityCriterion318.unit_evaluation_isIso
    (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.infinity A B)
    (WeierstrassGluing318.infinity_section A B)
  exact asIso (IntrinsicHodgeComparison318.evaluateAtSection
    (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.infinity A B)
    (WeierstrassGluing318.infinity_section A B) (SheafOfModules.unit _))

/-- The earlier invariant line pushforward equals the actual chart cotangent,
through canonical evaluation and the exact identity factorization. -/
@[expose] def invariantLinePushforwardToCotangent :
    (Scheme.Modules.pushforward (WeierstrassGluing318.structureMap A B)).obj
        (GlobalInvariantLine318.line A B) ≅ IdentityCotangent318.cotangent A B :=
  invariantLineEvaluationIso A B ≪≫ IdentityCotangent318.globalLineToCotangent A B

/-- The only remaining premise for intrinsic canonical Hodge invertibility over
a domain is now the actual global intrinsic differential-frame isomorphism.
Regular-function descent is a proved input, not a hypothesis. -/
theorem hodgeToIdentity_isIso_of_frame
    (frame : FamilyIntrinsicDifferentials318.familyOmega A B ≅ GlobalInvariantLine318.line A B) :
    IsIso (IntrinsicHodgeComparison318.hodgeToIdentity A B) := by
  letI := ProperAffineSections318.family_unitMap_isIso A B
  exact HodgeInvertibilityCriterion318.hodgeToIdentity_isIso A B frame

@[expose] def hodgeToIdentityIsoOfFrame
    (frame : FamilyIntrinsicDifferentials318.familyOmega A B ≅ GlobalInvariantLine318.line A B) :
    IntrinsicHodgeComparison318.hodge A B ≅ IntrinsicHodgeComparison318.identityCotangent A B := by
  letI := hodgeToIdentity_isIso_of_frame A B frame
  exact asIso (IntrinsicHodgeComparison318.hodgeToIdentity A B)
end DomainHodgeComparison318
