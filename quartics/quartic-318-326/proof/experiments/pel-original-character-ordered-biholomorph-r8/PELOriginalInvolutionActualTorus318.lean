module
public import PELOriginalTorusCoverLift318
public import ComplexTorusCoverPeriods318
public import ComplexCoverQuotientBiholomorph318
public section
noncomputable section
namespace PELOriginalInvolutionActualTorus318
open Set Topology
open scoped Manifold ContDiff
open PELOriginalInvolutionTower318 PELOriginalTorusCoverLift318
open ComplexLineLatticeAtlas318
variable (i:Fin 4)
local instance : ChartedSpace ℂ (InvolutionBase i):=
  PELOriginalInvolutionComplexAtlas318.involutionCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i):=
  PELOriginalInvolutionComplexAtlas318.involution_manifold i

/-- Constructed complete period subgroup of the actual original
involution quotient's complex-line lift. -/
@[expose] def periods : AddSubgroup ℂ:=
  ComplexTorusCoverPeriods318.periods (PELOriginalCharacterTorus318.periods i)
    (torusMap i) (torusMap_covering i) (origin i) (origin_over_zero i)
instance periods_discrete : DiscreteTopology (periods i):=
  ComplexTorusCoverPeriods318.periods_discrete _ _ _ _ _
local instance : ChartedSpace ℂ (Quotient (periods i)):=chartedSpace (periods i)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Quotient (periods i)):=complex_manifold (periods i)
lemma periods_le : periods i≤PELOriginalCharacterTorus318.periods i:=
  ComplexTorusCoverPeriods318.periods_le _ _ _ _ _
lemma lift_fiber (z w:ℂ) : universalLift i z=universalLift i w ↔ z-w∈periods i:=
  ComplexTorusCoverPeriods318.fiber_iff _ _ _ _ _ z w
lemma same_fibers (z w:ℂ) : projection (periods i) z=projection (periods i) w ↔
    universalLift i z=universalLift i w := by
  rw [lift_fiber]
  constructor
  · intro h
    apply QuotientAddGroup.eq_zero_iff.mp
    change (QuotientAddGroup.mk' (periods i))(z-w)=0
    rw [map_sub,h,sub_self]
  · intro h
    have hz:(QuotientAddGroup.mk' (periods i))(z-w)=0:=QuotientAddGroup.eq_zero_iff.mpr h
    rw [map_sub,sub_eq_zero] at hz
    exact hz

/-- The actual original InvolutionBase is biholomorphic to the quotient
by its PRODUCED complete period group. The topology and original atlas
are unchanged; no uniformization hypothesis remains on this consumer. -/
@[expose] def comparison : Quotient (periods i)≃ₜInvolutionBase i:=
  ComplexCoverQuotientBiholomorph318.comparison (periods i) (universalLift i)
    (universalLift_localHomeomorph i) (universalLift_surjective i) (same_fibers i)
lemma comparison_projection (z:ℂ) : comparison i (projection (periods i) z)=universalLift i z:=
  ComplexCoverQuotientBiholomorph318.comparison_projection _ _ _ _ _ z
lemma comparison_origin : comparison i 0=origin i:=by
  simpa only [show projection (periods i) 0=0 from rfl,universalLift_origin] using
    comparison_projection i 0
lemma comparison_original_map (z:ℂ) :
    toCharacterBase i (comparison i (projection (periods i) z))=
      PELOriginalCharacterTorus318.comparison i
        (projection (PELOriginalCharacterTorus318.periods i) z) := by
  rw [comparison_projection,universalLift_original_projection]
theorem biholomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i).symm:=
  ComplexCoverQuotientBiholomorph318.comparison_biholomorphic _ _ _ _ _
    (universalLift_holomorphic i)

/-- Original compactness now yields compact quotient for the produced
source periods, which is the input for the existing full rank-two basis
construction. Compactness is not another uniformization assumption. -/
instance quotient_compact : CompactSpace (Quotient (periods i)) := by
  apply isCompact_univ_iff.mp
  rw [←Set.range_eq_univ.mpr (comparison i).symm.surjective,←Set.image_univ]
  exact isCompact_univ.image (comparison i).symm.continuous
end PELOriginalInvolutionActualTorus318
