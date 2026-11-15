module
public import PELOriginalAllPowerComplexSections318
public import LineSheafTensorIsos318
public section
noncomputable section
namespace PELOriginalAlgebraicThetaSection318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalSectionMultiplication318
open PELOriginalWholeHZeroDimension318 PELOriginalLevelTheta318
open PELOriginalAllPowerFrameCoordinates318 PELOriginalAllPowerGlobalSections318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The actual tensor unit is removed by its genuine module-sheaf
isomorphism, not by relabeling L^1 as the original image/tensor line. -/
@[expose] def powerOneIso : Power τ hτ 1 ≅ sheaf τ hτ :=
  LineSheafTensorIsos318.leftUnit (line τ hτ)
@[expose] def sectionModule : Module ℂ Γ(sheaf τ hτ,⊤) :=
  Module.compHom Γ(sheaf τ hτ,⊤) (PELOriginalComplexSectionEquivalence318.base τ hτ)
local instance : Module ℂ Γ(sheaf τ hτ,⊤) := sectionModule τ hτ
local instance : Module ℂ Γ(Power τ hτ 1,⊤) := PELOriginalAllPowerComplexSections318.sectionModule τ hτ 1

@[expose] def powerOneSections : Γ(Power τ hτ 1,⊤) ≃ₗ[ℂ] Γ(sheaf τ hτ,⊤) where
  toFun := (powerOneIso τ hτ).hom.app ⊤
  invFun := (powerOneIso τ hτ).inv.app ⊤
  left_inv s := by
    have he := congrArg (fun f => f.app ⊤ s) (powerOneIso τ hτ).hom_inv_id
    exact he
  right_inv s := by
    have he := congrArg (fun f => f.app ⊤ s) (powerOneIso τ hτ).inv_hom_id
    exact he
  map_add' := map_add _
  map_smul' c s := by
    change (powerOneIso τ hτ).hom.app ⊤
      (PELOriginalComplexSectionEquivalence318.base τ hτ c • s)=
      PELOriginalComplexSectionEquivalence318.base τ hτ c • _
    exact map_smul _ _ _
@[expose] def sectionEquiv : homogeneous τ hτ 1 ≃ₗ[ℂ] Γ(sheaf τ hτ,⊤) :=
  (PELOriginalAllPowerComplexSections318.linearEquiv τ hτ 1).trans (powerOneSections τ hτ)

/-- A genuine global section of the SAME algebraic degree-one line,
whose cover representative is the ORIGINAL level-one theta function. -/
@[expose] def theta : Γ(sheaf τ hτ,⊤) := sectionEquiv τ hτ (thetaVector τ hτ 1 (0 : Label 1))
@[expose] def thetaMap : SheafOfModules.unit (candidate τ hτ).ringCatSheaf ⟶ sheaf τ hτ :=
  sectionMap τ hτ 1 (thetaVector τ hτ 1 (0 : Label 1))≫(powerOneIso τ hτ).hom
lemma theta_nonzero : theta τ hτ≠0 := by
  intro h
  have ho : thetaVector τ hτ 1 (0 : Label 1)=0 :=
    (sectionEquiv τ hτ).injective (h.trans (map_zero (sectionEquiv τ hτ)).symm)
  apply (PELOriginalLevelPowerSections318.sections_independent τ hτ 1).ne_zero (0 : Label 1)
  exact congrArg Subtype.val ho

/-- Exact inverse-frame coefficient of the original theta section on
EVERY mixed open, before any point specialization. -/
lemma theta_coefficient (a : NonemptyIndex τ hτ) :
    coefficient τ hτ 1 ((powerOneIso τ hτ).inv.app ⊤ (theta τ hτ)) a=
      PELOriginalAllPowerMixedCoefficients318.coefficient τ hτ 1 a (thetaVector τ hτ 1 (0 : Label 1)) := by
  change coefficient τ hτ 1 ((powerOneSections τ hτ).symm
    (powerOneSections τ hτ (algebraize τ hτ 1 (thetaVector τ hτ 1 (0 : Label 1))))) a=_
  rw [LinearEquiv.symm_apply_apply,coefficient_algebraize]

instance finiteDimensional : FiniteDimensional ℂ Γ(sheaf τ hτ,⊤) :=
  FiniteDimensional.of_surjective (sectionEquiv τ hτ).toLinearMap (sectionEquiv τ hτ).surjective
/-- Actual algebraic H0(L) is one-dimensional over its ORIGINAL
structural C scalars. This is not a count of a selected theta span. -/
theorem dimension_one : Module.finrank ℂ Γ(sheaf τ hτ,⊤)=1 := by
  rw [←(sectionEquiv τ hτ).finrank_eq,PELOriginalWholeHZeroDimension318.actual_hzero_dimension]
  norm_num

/-- Every actual global algebraic section of L is a scalar multiple
of this nonzero original theta section. No divisor smoothness follows yet. -/
theorem spans (s : Γ(sheaf τ hτ,⊤)) : ∃ c : ℂ,s=c • theta τ hτ := by
  obtain ⟨f,hf⟩ := expansionMap_surjective τ hτ 1 ((sectionEquiv τ hτ).symm s)
  refine ⟨f (0 : Label 1),?_⟩
  have he : (sectionEquiv τ hτ).symm s=f (0 : Label 1) • thetaVector τ hτ 1 (0 : Label 1) := by
    rw [←hf,expansionMap]
    simp
  have h := congrArg (sectionEquiv τ hτ) he
  simpa only [LinearEquiv.apply_symm_apply,map_smul,theta] using h
end PELOriginalAlgebraicThetaSection318
