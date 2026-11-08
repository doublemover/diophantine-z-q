module
public import ThreeTorsionSchemeBaseChange318
public import LiteralPrimitiveKernel318
public import ActualKernelBaseChange318
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public section
noncomputable section
namespace PrimitiveCoefficientSquares318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type} [CommRing R] [CommRing S] [Algebra R S]
variable [Invertible (3:R)] [Invertible (3:S)] (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
local notation "a" => algebraMap R S
local notation "hS" => CompletedKernelBaseChange318.mappedDiscriminant (S:=S) A B hD
local notation "c" => WeierstrassCoefficientMap318.coefficientMap (S:=S) A B

/-- The original completed primitive inclusion itself is cartesian, not only its base map. -/
theorem inclusion_cartesian : IsPullback (ThreeTorsionSchemeBaseChange318.schemeMap (S:=S) A B hD)
    (ThreeTorsionCompletedDoubling318.inclusion (a A) (a B) hS)
    (ThreeTorsionCompletedDoubling318.inclusion A B hD) c := by
  apply IsPullback.of_bot (v₂₁:=WeierstrassGluing318.structureMap (a A) (a B))
    (v₂₂:=WeierstrassGluing318.structureMap A B)
    (h₃₁:=Spec.map (CommRingCat.ofHom a))
  · simpa only [ThreeTorsionCompletedDoubling318.inclusion_over_base] using
      ThreeTorsionSchemeBaseChange318.isPullback (S:=S) A B hD
  · exact ThreeTorsionSchemeBaseChange318.completed_inclusion A B hD
  · exact WeierstrassBaseChange318.coefficient_base_pullback A B

/-- The actual zero section is cartesian for this same coefficient square. -/
theorem zero_cartesian : IsPullback (Spec.map (CommRingCat.ofHom a))
    (WeierstrassGluing318.infinity (a A) (a B)) (WeierstrassGluing318.infinity A B) c := by
  apply IsPullback.of_bot (v₂₁:=WeierstrassGluing318.structureMap (a A) (a B))
    (v₂₂:=WeierstrassGluing318.structureMap A B)
    (h₃₁:=Spec.map (CommRingCat.ofHom a))
  · simpa only [WeierstrassGluing318.infinity_section] using
      (IsPullback.of_id_snd (f:=Spec.map (CommRingCat.ofHom a)))
  · exact (WeierstrassCoefficientMap318.coefficientMap_infinity A B).symm
  · exact WeierstrassBaseChange318.coefficient_base_pullback A B

/-- Exact fiberwise zero locus after coefficient extension. This topological
range equality is used only to transport the nowhere-zero predicate. -/
theorem zero_range : Set.range (WeierstrassGluing318.infinity (a A) (a B))=
    c ⁻¹' Set.range (WeierstrassGluing318.infinity A B) := by
  rw [←(zero_cartesian (S:=S) A B).isoPullback_hom_snd,
    LiteralKernelFiniteRange318.range_comp_of_isIso]
  exact Scheme.Pullback.range_snd _ _
end PrimitiveCoefficientSquares318
