module
public import PELOriginalWholeSectionEquivalence318
public import PELOriginalCandidateChartBase318
public section
noncomputable section
namespace PELOriginalComplexSectionEquivalence318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalCandidateChartBase318
open PELOriginalLevelTheta318 PELOriginalSectionMultiplication318
open PELOriginalWholeCubicFrames318 PELOriginalWholeCubicRegularCoefficients318
open PELOriginalAlgebraicSectionRecovery318 PELOriginalWholeSectionEquivalence318
variable (τ : ℂ) (hτ : 0 < τ.im) (m : ℕ)

/-- The ACTUAL original structural complex scalar map, not a map
transported through the holomorphic-section equivalence. -/
@[expose] def base : ℂ →+* Γ(candidate τ hτ,⊤) :=
  (PELOriginalProperComplexCandidate318.structureMap τ hτ).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
@[expose] def sectionModule : Module ℂ Γ(Power τ hτ m,⊤) :=
  Module.compHom Γ(Power τ hτ m,⊤) (base τ hτ)
local instance : Module ℂ Γ(Power τ hτ m,⊤) := sectionModule τ hτ m

/-- Full structural scalar square through the SAME whole affine chart. -/
lemma coefficient_base (j : Label 3) (c : ℂ) :
    coefficientEquiv τ hτ j ((candidate τ hτ).presheaf.map
      (homOfLE (show candidateChart τ hτ j ≤ ⊤ from le_top)).op (base τ hτ c))=
      algebraMap ℂ (CoordinateChart τ hτ j) c := by
  have hr : (LineFrameTopScalar318.ringTop (candidateChart τ hτ j)).inv
      ((candidate τ hτ).presheaf.map (homOfLE le_top).op (base τ hτ c))=
      (candidateChart τ hτ j).ι.appTop (base τ hτ c) := by
    rw [Scheme.Opens.ι_appTop]
    change (candidate τ hτ).presheaf.map _ ((candidate τ hτ).presheaf.map _ (base τ hτ c))=_
    rw [←Functor.map_comp]
    rfl
  change (Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ j))).hom
    ((actualChartIso τ hτ j).hom.appTop
      ((LineFrameTopScalar318.ringTop (candidateChart τ hτ j)).inv _))=_
  rw [hr]
  change (Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ j))).hom
    ((chartMap τ hτ j≫PELOriginalProperComplexCandidate318.structureMap τ hτ).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))=_
  rw [chart_over_complex_base]
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (algebraMap ℂ (CoordinateChart τ hτ j))))
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
  simpa only [Iso.inv_hom_id_apply] using h

lemma element_smul (c : ℂ) (s : Γ(Power τ hτ m,⊤)) (j : Label 3) :
    element τ hτ m (c • s) j=c • element τ hτ m s j := by
  change coefficientEquiv τ hτ j
    ((OpenLineFrameCoordinates318.frame (Power τ hτ m) (candidateChart τ hτ j)
      (powerFrame τ hτ m j) (candidateChart τ hτ j) le_rfl).symm
      ((Power τ hτ m).presheaf.map (homOfLE le_top).op (base τ hτ c • s)))=_
  rw [(Power τ hτ m).val.map_smul,map_smul,smul_eq_mul,map_mul,coefficient_base]
  rfl

lemma algebraize_smul (c : ℂ) (s : homogeneous τ hτ (3*m)) :
    algebraize τ hτ m (c • s)=c • algebraize τ hτ m s := by
  apply elements_injective τ hτ m
  funext j
  rw [element_algebraize,element_smul,element_algebraize,map_smul]

/-- Full complex-linear section comparison over the ORIGINAL structural
complex scalars. Both inverses are the previously constructed genuine
regular/holomorphic recovery maps. -/
@[expose] def linearEquiv : homogeneous τ hτ (3*m) ≃ₗ[ℂ] Γ(Power τ hτ m,⊤) :=
  { additiveEquiv τ hτ m with map_smul' := algebraize_smul τ hτ m }

/-- Actual algebraic section dimension equals the full original
holomorphic section dimension, for every m including degree zero. -/
theorem finrank_eq : Module.finrank ℂ Γ(Power τ hτ m,⊤)=
    Module.finrank ℂ (homogeneous τ hτ (3*m)) :=
  (linearEquiv τ hτ m).finrank_eq.symm
end PELOriginalComplexSectionEquivalence318
