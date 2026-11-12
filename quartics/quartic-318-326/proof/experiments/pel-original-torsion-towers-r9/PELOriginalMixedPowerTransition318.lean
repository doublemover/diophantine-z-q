module
public import PELOriginalMixedPowerUnit318
public section
noncomputable section
namespace PELOriginalMixedPowerTransition318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalMixedRatioCover318 PELOriginalMixedPointEvaluation318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateReduced : IsReduced (candidate τ hτ) := reduced τ hτ

/-- The actual regular degree-six bridge on the WHOLE mixed overlap.
It proves the precise gauge relation between the cubic-square and
quadratic-cube line cocycles before any analytic comparison is used. -/
theorem power_transition (a b : Index) :
    (toRight τ hτ a b).appTop (PELOriginalMixedPowerUnit318.value τ hτ b) *
        ((toLeft τ hτ a b).appTop (cubic τ hτ a b.1))^2 =
    (toLeft τ hτ a b).appTop (PELOriginalMixedPowerUnit318.value τ hτ a) *
        ((toLeft τ hτ a b).appTop (quadratic τ hτ a b.2))^3 := by
  let π := (overlap τ hτ a b).ι ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ
  letI : LocallyOfFiniteType π := by dsimp [π]; infer_instance
  apply ReducedSchemeGlobalFunctionSeparation318.ext π
  intro p hp
  let pL := p ≫ toLeft τ hτ a b
  let pR := p ≫ toRight τ hτ a b
  have hL : pL ≫ (mixedOpen τ hτ a).ι ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ = 𝟙 _ := by
    simpa only [pL,toLeft,Category.assoc,Scheme.homOfLE_ι_assoc] using hp
  obtain ⟨z,h3a,h2a,hA,heL⟩ := point_representation τ hτ a pL hL
  have heR : pR ≫ (mixedOpen τ hτ b).ι = candidateComplexPoint τ hτ (projection (P τ) z) := by
    simpa only [pR,pL,toRight,toLeft,Category.assoc,Scheme.homOfLE_ι] using heL
  obtain ⟨h3b,h2b⟩ := coordinates_nonzero τ hτ b pR z heR
  apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.injective
  simp only [map_mul,map_pow]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (pR.appTop (PELOriginalMixedPowerUnit318.value τ hτ b)) *
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (pL.appTop (cubic τ hτ a b.1)))^2 =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (pL.appTop (PELOriginalMixedPowerUnit318.value τ hτ a)) *
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (pL.appTop (quadratic τ hτ a b.2)))^3
  rw [PELOriginalMixedPowerUnit318.evaluation τ hτ b pR z h3b heR,
    PELOriginalMixedPowerUnit318.evaluation τ hτ a pL z h3a heL,
    cubic_evaluation τ hτ a b.1 pL hL z h3a heL,
    quadratic_evaluation τ hτ a b.2 pL hL z h2a heL]
  field_simp [h3a,h3b,h2a,h2b]
  <;> ring

/-- Both sides are literal regular UNITS, hence the relation upgrades
to the exact unit-cocycle gauge equation without discarding zero loci. -/
theorem power_units (a b : Index) :
    Units.map (toRight τ hτ a b).appTop.hom.toMonoidHom (PELOriginalMixedPowerUnit318.unit τ hτ b) *
      (cubic_unit τ hτ a b).unit^2 =
    Units.map (toLeft τ hτ a b).appTop.hom.toMonoidHom (PELOriginalMixedPowerUnit318.unit τ hτ a) *
      (quadratic_unit τ hτ a b).unit^3 := by
  apply Units.ext
  simpa only [Units.val_mul,Units.val_pow_eq_pow_val,Units.coe_map,PELOriginalMixedPowerUnit318.unit_value,
    IsUnit.unit_spec] using power_transition τ hτ a b
end PELOriginalMixedPowerTransition318
