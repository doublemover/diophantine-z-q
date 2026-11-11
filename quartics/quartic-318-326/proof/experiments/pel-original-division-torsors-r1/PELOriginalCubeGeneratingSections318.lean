module
public import PELOriginalPolarizationCube318
public import RestrictedFreeScalarRow318
public section
noncomputable section
namespace PELOriginalCubeGeneratingSections318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalReducedProjectiveCandidate318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalMixedRatioCover318 PELOriginalLevelTheta318
variable (τ : ℂ) (hτ : 0 < τ.im)

abbrev cube := (LineSheafTensorPower318.line (line τ hτ) 3).object

/-- Nine actual global generating sections of the THIRD intrinsic tensor
power of the degree-one algebraic line, transported through the proved
whole-sheaf cube isomorphism. -/
@[expose] def section (i : Label 3) :
    SheafOfModules.unit (candidate τ hτ).ringCatSheaf ⟶ cube τ hτ :=
  cubicSection τ hτ i ≫ (PELOriginalPolarizationCube318.cubeIso τ hτ).inv

@[expose] def presentation :
    SheafOfModules.free (R := (candidate τ hτ).ringCatSheaf) (Label 3) ⟶ cube τ hτ :=
  factorThruImage (ChartGeneratedImageSheaf318.presentation
    (opens τ hτ (anchor τ hτ)).ι (cubic τ hτ (anchor τ hτ).val)) ≫
      (PELOriginalPolarizationCube318.cubeIso τ hτ).inv

/-- This is an EPIMORPHISM of complete module sheaves, not just
surjectivity of fibers or an assumed global-generation label. -/
instance presentation_epi : Epi (presentation τ hτ) := by
  dsimp [presentation]
  infer_instance

@[reassoc] theorem generator (i : Label 3) :
    SheafOfModules.ιFree i ≫ presentation τ hτ = section τ hτ i := by
  simp only [presentation,section,cubicSection,Category.assoc]

/-- Actual local frames of the SAME tensor cube, normalized so that
its transported coordinate sections retain their original ratios. -/
@[expose] def frame (a : NonemptyIndex τ hτ) :
    SheafOfModules.unit (opens τ hτ a).toScheme.ringCatSheaf ≅
      (cube τ hτ).restrict (opens τ hτ a).ι :=
  cubicFrame τ hτ a ≪≫ (Scheme.Modules.restrictFunctor (opens τ hτ a).ι).mapIso
    (PELOriginalPolarizationCube318.cubeIso τ hτ).symm

/-- Exact full sheaf coefficient identity on every mixed chart. -/
theorem section_coefficient (a : NonemptyIndex τ hτ) (i : Label 3) :
    (Scheme.Modules.restrictUnitIso (opens τ hτ a).ι).inv ≫
      (Scheme.Modules.restrictFunctor (opens τ hτ a).ι).map (section τ hτ i) =
    GlobalScalarSheafEndomorphism318.endomorphism _ (cubic τ hτ a.val i) ≫
      (frame τ hτ a).hom := by
  simp only [section,Functor.map_comp,←Category.assoc]
  rw [cubic_section_coefficient]
  rfl

/-- The distinguished coordinate is literally the chosen frame;
there is no residual scalar ambiguity in the projective realization. -/
theorem distinguished_section (a : NonemptyIndex τ hτ) :
    (Scheme.Modules.restrictUnitIso (opens τ hτ a).ι).inv ≫
      (Scheme.Modules.restrictFunctor (opens τ hτ a).ι).map (section τ hτ a.val.1) =
      (frame τ hτ a).hom := by
  rw [section_coefficient,cubic_self,GlobalScalarSheafEndomorphism318.endomorphism_one,
    Category.id_comp]

/-- Full free-presentation equality, retaining the original scalar
row and the transported actual rank-one frame. -/
theorem presentation_in_frame (a : NonemptyIndex τ hτ) :
    RestrictedFreeScalarRow318.row (opens τ hτ a).ι (cubic τ hτ a.val) ≫
      (frame τ hτ a).hom =
    (Scheme.Modules.restrictFunctor (opens τ hτ a).ι).map (presentation τ hτ) := by
  apply RestrictedFreeScalarRow318.factorization
  intro i
  rw [generator]
  have h := section_coefficient τ hτ a i
  have h' := congrArg (fun f => (Scheme.Modules.restrictUnitIso (opens τ hτ a).ι).hom ≫ f) h
  simpa only [←Category.assoc,Iso.hom_inv_id,Category.id_comp] using h'
end PELOriginalCubeGeneratingSections318
