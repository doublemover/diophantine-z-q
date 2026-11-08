module
public import IntrinsicFamilyFrames318
public import IntrinsicHodgeComparison318
public section
noncomputable section
namespace IntrinsicIdentityFrame318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (A B : R)

/-- The identity pullback of intrinsic global Omega is the actual infinity-chart
cotangent sheaf previously constructed. This uses the proved intrinsic chart
comparison, not a supplied global Omega frame. -/
@[expose] def toCotangent :
    IntrinsicHodgeComparison318.identityCotangent A B ≅ IdentityCotangent318.cotangent A B :=
  ((Scheme.Modules.pullbackCongr (IdentityCotangent318.infinity_factorization A B)).app _).symm ≪≫
  ((Scheme.Modules.pullbackComp (InfinityChart318.sectionAtInfinity A B)
      (InvariantChartCover318.infinityInto A B)).app _).symm ≪≫
  (Scheme.Modules.pullback (InfinityChart318.sectionAtInfinity A B)).mapIso
    (((Scheme.Modules.restrictFunctorIsoPullback (InvariantChartCover318.infinityInto A B)).app _).symm ≪≫
      IntrinsicFamilyFrames318.infinityIdentification A B)

/-- Actual intrinsic identity cotangent is a free O-base line, without a global
Hodge-isomorphism assumption. -/
@[expose] def frame :
    IntrinsicHodgeComparison318.identityCotangent A B ≅
      SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf :=
  toCotangent A B ≪≫ IdentityCotangent318.cotangentFrame A B

@[expose] def literalFrame (N : ℕ) :=
  frame (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
end IntrinsicIdentityFrame318
