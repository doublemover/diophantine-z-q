module
public import PELPrincipalProperAction318
public import Mathlib.Topology.Covering.Quotient
public section
noncomputable section
namespace PELPrincipalThreeCovering318
open QuaternionicJointPeriodTopology318 PELJointPeriodFamily318 PELJointPeriodDeck318
open PELJointComplexAtlas318 PELJointArithmeticLift318 PELJointArithmeticCoherence318
open PELPrincipalThreeFreeAction318 PELOriginalDiscreteSLGroup318 PELPrincipalProperAction318
open scoped Manifold ContDiff
set_option maxHeartbeats 1400000
local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold
local instance : LocallyCompactSpace HalfPlane :=
  (baseChart.isOpenEmbedding rfl).locallyCompactSpace
local instance : T2Space ReferenceSurface :=
  PELComplexPeriodSurface318.surface_hausdorff basePoint basePoint.property
local instance : CompactSpace ReferenceSurface :=
  PELComplexPeriodSurface318.surface_compact basePoint basePoint.property

@[expose] def fromUpper (τ : UpperHalfPlane) : HalfPlane := ⟨τ,τ.im_pos⟩
theorem fromUpper_continuous : Continuous fromUpper := UpperHalfPlane.continuous_coe.subtype_mk _

instance base_continuous : ContinuousConstSMul principalThree HalfPlane where
  continuous_const_smul u := by
    have h := fromUpper_continuous.comp
      ((continuous_const_smul (intoImage u)).comp toUpper_continuous)
    change Continuous (fun τ => fromUpper (intoImage u • toUpper τ)) at h
    have he : (fun τ => fromUpper (intoImage u • toUpper τ))=(fun τ => u • τ) := by
      funext τ
      rw [←toUpper_equivariant]
      rfl
    rwa [he] at h

instance total_continuous : ContinuousConstSMul principalThree Total where
  continuous_const_smul u :=
    (PELJointArithmeticHolomorphy318.totalAction_holomorphic u.val (determinant u)).continuous

instance base_free : IsCancelSMul principalThree HalfPlane :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr (fun u τ h => no_base_stabilizer u τ h)
instance total_free : IsCancelSMul principalThree Total :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr no_total_stabilizer

/-- The literal orbit quotient by the precise original principal-three
arithmetic group, with the standard quotient topology. -/
abbrev ArithmeticBase := Quotient (MulAction.orbitRel principalThree HalfPlane)
abbrev ArithmeticTotal := Quotient (MulAction.orbitRel principalThree Total)
@[expose] def baseQuotient : HalfPlane → ArithmeticBase := Quotient.mk _
@[expose] def totalQuotient : Total → ArithmeticTotal := Quotient.mk _

/-- All hypotheses for the actual base quotient covering are constructed:
original discrete image, proper discontinuity, continuity and exact freeness. -/
theorem base_covering : IsQuotientCoveringMap baseQuotient principalThree :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem total_covering : IsQuotientCoveringMap totalQuotient principalThree :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem base_localHomeomorph : IsLocalHomeomorph baseQuotient := base_covering.isLocalHomeomorph
theorem total_localHomeomorph : IsLocalHomeomorph totalQuotient := total_covering.isLocalHomeomorph

/-- The arithmetic-family projection is actually descended through BOTH
orbit relations. Its source and base are the same original level-three quotients. -/
@[expose] def arithmeticProjection : ArithmeticTotal → ArithmeticBase :=
  Quotient.map' Prod.fst (by
    rintro p q ⟨u,hu⟩
    exact ⟨u,congrArg Prod.fst hu⟩)

theorem arithmeticProjection_continuous : Continuous arithmeticProjection :=
  continuous_fst.quotient_map' _

theorem arithmetic_projection_square (p : Total) :
    arithmeticProjection (totalQuotient p)=baseQuotient p.1 := rfl

/-- A genuine quotient family now exists topologically. Descending its
complex atlas, relative group/polarization and algebraization remain separate. -/
theorem totalQuotient_surjective : Function.Surjective totalQuotient := Quotient.mk_surjective
theorem baseQuotient_surjective : Function.Surjective baseQuotient := Quotient.mk_surjective
end PELPrincipalThreeCovering318
