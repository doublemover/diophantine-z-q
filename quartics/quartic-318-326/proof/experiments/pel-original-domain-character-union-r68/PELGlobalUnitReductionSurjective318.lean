module
public import PELGlobalIntegralUnitLifts318
public section
noncomputable section
namespace PELGlobalUnitReductionSurjective318
open PELPrincipalOrderCoordinates318 PELOrderReductionThree318 PELGlobalIntegralUnitLifts318
set_option maxHeartbeats 1000000

@[expose] def unitReduction : orderˣ →* Reductionˣ := Units.map reduction.toMonoidHom

theorem unitReduction_surjective : Function.Surjective unitReduction := by
  intro u
  have hu : PELReductionResidueField318.residue (u:Reduction)≠0 :=
    (u.isUnit.map PELReductionResidueField318.residue).ne_zero
  obtain ⟨k,a,b,h⟩ := finite_cover (u:Reduction) hu
  refine ⟨globalWord k a b,?_⟩
  apply Units.ext
  change reduction (globalWord k a b:order)=(u:Reduction)
  rw [word_reduction]
  exact h

@[expose] def originalUnitReduction : orderˣ →* QuotientOrderˣ :=
  Units.map moduloThree.mk'.toMonoidHom

/-- Surjectivity is on units of literal O/3O, not merely the related finite
quaternion presentation or semisimple residue field. -/
theorem originalUnitReduction_surjective : Function.Surjective originalUnitReduction := by
  intro u
  obtain ⟨v,hv⟩ := unitReduction_surjective (Units.mapEquiv quotientEquiv.toMulEquiv u)
  refine ⟨v,?_⟩
  apply Units.ext
  apply quotientEquiv.injective
  change reduction (v:order)=quotientEquiv (u:QuotientOrder)
  exact congrArg (fun w : Reductionˣ => (w:Reduction)) hv

/-- The same full global unit group surjects onto the actual36-element
projective unit quotient. No positive-unit or norm-one image is enlarged. -/
@[expose] def projectiveReduction : orderˣ →*
    PELNormalizerProjectiveLevel318.EffectiveLevel :=
  (QuotientGroup.mk' (LevelThreeKernel318.signs QuotientOrder)).comp originalUnitReduction

theorem projectiveReduction_surjective : Function.Surjective projectiveReduction := by
  intro x
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (LevelThreeKernel318.signs QuotientOrder) x
  obtain ⟨v,rfl⟩ := originalUnitReduction_surjective u
  exact ⟨v,rfl⟩
end PELGlobalUnitReductionSurjective318
