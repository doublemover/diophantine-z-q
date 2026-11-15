module
public import IntrinsicGlobalFrame318
public import DomainHodgeComparison318
public import IntrinsicIdentityFrame318
public section
noncomputable section
namespace IntrinsicHodgeIsomorphism318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] (A B : R)
    (hD : IsUnit (-16*(4*A^3+27*B^2)))
include hD

/-- Canonical evaluation of genuine relative differentials at the actual
infinity section is an isomorphism for the smooth completed Weierstrass family
over every domain base. Both the global differential frame and structure-sheaf
pushforward descent are proved inputs. -/
theorem hodgeToIdentity_isIso : IsIso (IntrinsicHodgeComparison318.hodgeToIdentity A B) :=
  DomainHodgeComparison318.hodgeToIdentity_isIso_of_frame A B (IntrinsicGlobalFrame318.frame A B hD)

@[expose] def hodgeToIdentityIso : IntrinsicHodgeComparison318.hodge A B ≅
    IntrinsicHodgeComparison318.identityCotangent A B := by
  letI := hodgeToIdentity_isIso A B hD
  exact asIso (IntrinsicHodgeComparison318.hodgeToIdentity A B)

/-- The Hodge line of the actual complete family, identified with its actual
infinity-chart cotangent through the canonical evaluation map. -/
@[expose] def hodgeToCotangent : IntrinsicHodgeComparison318.hodge A B ≅
    IdentityCotangent318.cotangent A B :=
  hodgeToIdentityIso A B hD ≪≫ IntrinsicIdentityFrame318.toCotangent A B

@[expose] def hodgeFrame : IntrinsicHodgeComparison318.hodge A B ≅
    SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf :=
  hodgeToIdentityIso A B hD ≪≫ IntrinsicIdentityFrame318.frame A B

/-- The comparison is the pre-existing canonical evaluation morphism, not an
arbitrarily chosen isomorphism between abstract rank-one sheaves. -/
theorem hodgeToIdentityIso_hom : (hodgeToIdentityIso A B hD).hom=
    IntrinsicHodgeComparison318.hodgeToIdentity A B := rfl
end IntrinsicHodgeIsomorphism318
