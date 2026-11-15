module
public import PELOriginalAllPowerSectionEquivalence318
public import PELOriginalComplexSectionEquivalence318
public section
noncomputable section
namespace PELOriginalAllPowerComplexSections318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalAllPowerFrameCoordinates318 PELOriginalAllPowerGlobalSections318
open PELOriginalAllPowerSectionEquivalence318 PELOriginalSectionMultiplication318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalTranslationFrameValues318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℕ)
abbrev base := PELOriginalComplexSectionEquivalence318.base τ hτ
/-- Actual structural scalars, not an action transported through a
section equivalence. -/
@[expose] def sectionModule : Module ℂ Γ(Power τ hτ n,⊤) :=
  Module.compHom Γ(Power τ hτ n,⊤) (base τ hτ)
local instance : Module ℂ Γ(Power τ hτ n,⊤) := sectionModule τ hτ n

lemma coefficient_smul (c : ℂ) (s : Γ(Power τ hτ n,⊤)) (a : NonemptyIndex τ hτ) :
    coefficient τ hτ n (c • s) a=
      (candidate τ hτ).presheaf.map (homOfLE le_top).op (base τ hτ c)*coefficient τ hτ n s a := by
  change (OpenLineFrameCoordinates318.frame (Power τ hτ n) (opens τ hτ a)
    (frame τ hτ n a) (opens τ hτ a) le_rfl).symm
      ((Power τ hτ n).presheaf.map (homOfLE le_top).op (base τ hτ c • s))=_
  rw [(Power τ hτ n).val.map_smul,map_smul,smul_eq_mul]
  rfl

lemma base_value (U : (candidate τ hτ).Opens) (c : ℂ) (z : ComplexVectors)
    (hz : z∈domain τ hτ U) :
    value τ hτ U ((candidate τ hτ).presheaf.map (homOfLE le_top).op (base τ hτ c)) z=c := by
  let p := point τ hτ U z hz
  have hp : p≫U.ι≫PELOriginalProperComplexCandidate318.structureMap τ hτ=𝟙 _ := by
    rw [←Category.assoc,point_ι,PELOriginalProperComplexCandidate318.candidate_point_over]
  rw [value_at_point τ hτ U _ z p (point_ι τ hτ U z hz)]
  have hr : (LineFrameTopScalar318.ringTop U).inv
      ((candidate τ hτ).presheaf.map (homOfLE le_top).op (base τ hτ c))=
      U.ι.appTop (base τ hτ c) := by
    rw [Scheme.Opens.ι_appTop]
    change (candidate τ hτ).presheaf.map _
      ((candidate τ hτ).presheaf.map _ (base τ hτ c))=_
    rw [←Functor.map_comp]
    rfl
  rw [hr]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((p≫U.ι≫PELOriginalProperComplexCandidate318.structureMap τ hτ).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))=_
  rw [hp]
  simpa only [Scheme.Hom.id_appTop,CommRingCat.id_apply] using
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply c

lemma algebraize_smul (c : ℂ) (s : homogeneous τ hτ n) :
    algebraize τ hτ n (c • s)=c • algebraize τ hτ n s := by
  apply coefficients_injective τ hτ n
  funext a
  rw [coefficient_algebraize,coefficient_smul,coefficient_algebraize]
  apply PELOriginalOpenFunctionSeparation318.ext τ hτ (opens τ hτ a)
  intro z hz
  rw [value_mul τ hτ _ _ _ z hz,base_value,
    PELOriginalAllPowerMixedCoefficients318.coefficient_value τ hτ n a (c • s) z hz,
    PELOriginalAllPowerMixedCoefficients318.coefficient_value τ hτ n a s z hz]
  simp only [PELOriginalPowerSectionLift318.lift,PELOriginalWholeHZeroDimension318.asSection,
    Submodule.coe_smul,Pi.smul_apply,smul_eq_mul]
  ring

/-- Full all-degree section comparison over the ORIGINAL complex
structure map. In particular degree one and degree two are included. -/
@[expose] def linearEquiv : homogeneous τ hτ n ≃ₗ[ℂ] Γ(Power τ hτ n,⊤) :=
  { additiveEquiv τ hτ n with map_smul' := algebraize_smul τ hτ n }
theorem finrank_eq : Module.finrank ℂ Γ(Power τ hτ n,⊤)=Module.finrank ℂ (homogeneous τ hτ n) :=
  (linearEquiv τ hτ n).finrank_eq.symm
instance finiteDimensional [NeZero n] : FiniteDimensional ℂ Γ(Power τ hτ n,⊤) :=
  FiniteDimensional.of_surjective (linearEquiv τ hτ n).toLinearMap (linearEquiv τ hτ n).surjective
/-- Actual algebraic H0(L^n) has dimension n², for every positive n. -/
theorem dimension [NeZero n] : Module.finrank ℂ Γ(Power τ hτ n,⊤)=n^2 := by
  rw [finrank_eq]
  exact PELOriginalWholeHZeroDimension318.actual_hzero_dimension τ hτ n
end PELOriginalAllPowerComplexSections318
