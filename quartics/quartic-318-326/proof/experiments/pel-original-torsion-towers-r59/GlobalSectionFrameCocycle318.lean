module
public import GlobalSectionFrameCoordinates318
public import LineFrameCocycle318
public section
noncomputable section
namespace GlobalSectionFrameCocycle318
open AlgebraicGeometry CategoryTheory Opposite
universe u v
variable {X : Scheme.{u}} (M : X.Modules) {ι : Type v} (U : ι → X.Opens)
  (e : ∀ i, SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (σ : SheafOfModules.unit X.ringCatSheaf ⟶ M)

/-- A section that is the chosen right frame fixes the extracted
left-to-right cocycle EXACTLY. Both hypotheses are full module-sheaf
identities and the conclusion lives in the original overlap ring. -/
theorem transition_value (i j : ι) (r : Γ((U i).toScheme,⊤))
    (hi : (Scheme.Modules.restrictUnitIso (U i).ι).inv ≫
      (Scheme.Modules.restrictFunctor (U i).ι).map σ =
        GlobalScalarSheafEndomorphism318.endomorphism (U i).toScheme r ≫ (e i).hom)
    (hj : (Scheme.Modules.restrictUnitIso (U j).ι).inv ≫
      (Scheme.Modules.restrictFunctor (U j).ι).map σ = (e j).hom) :
    ((LineFrameCocycle318.cocycle M U e).transition i j).val =
      GlobalSectionFrameCoordinates318.coefficient (U i) r (U i ⊓ U j) inf_le_left := by
  have hj' : (Scheme.Modules.restrictUnitIso (U j).ι).inv ≫
      (Scheme.Modules.restrictFunctor (U j).ι).map σ =
        GlobalScalarSheafEndomorphism318.endomorphism (U j).toScheme 1 ≫ (e j).hom := by
    simpa only [GlobalScalarSheafEndomorphism318.endomorphism_one,Category.id_comp] using hj
  have hiC := GlobalSectionFrameCoordinates318.coefficient_formula M (U i) (e i) σ r hi
    (U i ⊓ U j) inf_le_left
  have hjC := GlobalSectionFrameCoordinates318.coefficient_formula M (U j) (e j) σ 1 hj'
    (U i ⊓ U j) inf_le_right
  simp only [GlobalSectionFrameCoordinates318.coefficient,map_one] at hjC
  apply (OpenLineFrameCoordinates318.frame M (U i) (e i) (U i ⊓ U j) inf_le_left).injective
  have hr := LineFrameTransitions318.relation M U e i j (U i ⊓ U j) inf_le_left inf_le_right 1
  simpa only [mul_one] using hr.trans (hjC.trans hiC.symm)

/-- The computed coefficient is automatically a genuine UNIT because
it equals the actual frame transition, without any extra pointwise
nonvanishing or normality premise. -/
theorem coefficient_isUnit (i j : ι) (r : Γ((U i).toScheme,⊤))
    (hi : (Scheme.Modules.restrictUnitIso (U i).ι).inv ≫
      (Scheme.Modules.restrictFunctor (U i).ι).map σ =
        GlobalScalarSheafEndomorphism318.endomorphism (U i).toScheme r ≫ (e i).hom)
    (hj : (Scheme.Modules.restrictUnitIso (U j).ι).inv ≫
      (Scheme.Modules.restrictFunctor (U j).ι).map σ = (e j).hom) :
    IsUnit (GlobalSectionFrameCoordinates318.coefficient (U i) r (U i ⊓ U j) inf_le_left) := by
  rw [←transition_value M U e σ i j r hi hj]
  exact Units.isUnit _

/-- Unit-valued equality retains the literal prescribed regular ratio,
so later Spec(C) specialization follows by mapping a proved algebraic
identity rather than defining the cocycle through analytic points. -/
theorem transition_eq (i j : ι) (r : Γ((U i).toScheme,⊤))
    (hi : (Scheme.Modules.restrictUnitIso (U i).ι).inv ≫
      (Scheme.Modules.restrictFunctor (U i).ι).map σ =
        GlobalScalarSheafEndomorphism318.endomorphism (U i).toScheme r ≫ (e i).hom)
    (hj : (Scheme.Modules.restrictUnitIso (U j).ι).inv ≫
      (Scheme.Modules.restrictFunctor (U j).ι).map σ = (e j).hom) :
    (LineFrameCocycle318.cocycle M U e).transition i j =
      (coefficient_isUnit M U e σ i j r hi hj).unit := by
  apply Units.ext
  rw [IsUnit.unit_spec]
  exact transition_value M U e σ i j r hi hj
end GlobalSectionFrameCocycle318
