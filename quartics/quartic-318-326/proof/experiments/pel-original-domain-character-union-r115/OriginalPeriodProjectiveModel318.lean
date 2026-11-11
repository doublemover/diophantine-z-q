module
public import OriginalPeriodEllipticGroup318
public import CubicClosedImmersion318
public section
noncomputable section
namespace OriginalPeriodProjectiveModel318
open CategoryTheory AlgebraicGeometry OriginalComplexPeriodPair318
open ComplexAffineFreeTranslation318
set_option maxHeartbeats 1800000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]
@[expose] def A : ℂ := -(pair L).g₂/4
@[expose] def B : ℂ := -(pair L).g₃/4

/-- The coefficients are exactly those of the independently constructed
native elliptic curve, with its original Pprime/2 coordinate convention. -/
lemma native_coefficients :
    (OriginalPeriodEllipticPoints318.curve L).a₄=A L ∧
    (OriginalPeriodEllipticPoints318.curve L).a₆=B L := by
  constructor <;> dsimp [OriginalPeriodEllipticPoints318.curve,NormalizedWeierstrass318.model,A,B] <;> ring
lemma discriminant : -16*(4*A L^3+27*B L^2)=(pair L).g₂^3-27*(pair L).g₃^2 := by
  dsimp [A,B]
  ring
lemma discriminant_unit : IsUnit (-16*(4*A L^3+27*B L^2)) := by
  rw [isUnit_iff_ne_zero,discriminant]
  exact WeierstrassCubicNonsingular318.discriminant_ne_zero _

/-- Actual original-coefficient projective cubic SCHEME, constructed
from its finite and infinity affine rings with their genuine localization
isomorphism. No analytic equivalence is used to define its geometry. -/
abbrev model := WeierstrassGluing318.scheme (A L) (B L)
abbrev structure := WeierstrassGluing318.structureMap (A L) (B L)
abbrev embedding := CubicProjectiveMap318.embedding (A L) (B L)
abbrev infinity := WeierstrassGluing318.infinity (A L) (B L)

theorem smooth : Smooth (structure L) :=
  WeierstrassGluing318.structure_smooth _ _ (discriminant_unit L)
theorem proper : IsProper (structure L) := CubicClosedImmersion318.structure_proper _ _
theorem separated : IsSeparated (structure L) := CubicClosedImmersion318.structure_separated _ _
theorem projective_embedding : IsClosedImmersion (embedding L) :=
  CubicClosedImmersion318.embedding_closed _ _
theorem embedding_over_base : embedding L ≫ ProjectivePlane318.structureMap ℂ=structure L :=
  CubicChartGeometry318.embedding_over_base _ _
theorem infinity_section : infinity L ≫ structure L=𝟙 _ :=
  WeierstrassGluing318.infinity_section _ _
end OriginalPeriodProjectiveModel318
