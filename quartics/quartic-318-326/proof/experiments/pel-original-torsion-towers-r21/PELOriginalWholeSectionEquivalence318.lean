module
public import PELOriginalWholeCubicRegularCoefficients318
public import FramedLineCoefficientGluing318
public section
noncomputable section
namespace PELOriginalWholeSectionEquivalence318
open AlgebraicGeometry CategoryTheory
open PELOriginalCandidateAffineCharts318 PELOriginalReducedProjectiveCandidate318
open PELOriginalLevelTheta318 PELOriginalSectionMultiplication318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalWholeCubicFrames318
open PELOriginalAlgebraicSectionRecovery318 PELOriginalWholeCubicRegularCoefficients318
variable (τ : ℂ) (hτ : 0 < τ.im) (m : ℕ)

/-- Full original-section algebraization in the same whole cubic power
sheaf, using the normalized whole affine frames. -/
@[expose] def algebraize (s : homogeneous τ hτ (3*m)) : Γ(Power τ hτ m,⊤) :=
  FramedLineCoefficientGluing318.global (Power τ hτ m) (candidateChart τ hτ)
    (powerFrame τ hτ m) (regularCoefficient τ hτ m s)
    (fun j k => by
      simpa only [powerFrame,FramedLineTensorPower318.transition,Units.val_pow_eq_pow_val]
        using PELOriginalWholeCubicRegularCoefficients318.transition τ hτ m s j k)
    (coversTop τ hτ)

lemma algebraize_restrict (s : homogeneous τ hτ (3*m)) (j : Label 3) :
    (Power τ hτ m).presheaf.map (homOfLE (show candidateChart τ hτ j ≤ ⊤ from le_top)).op
      (algebraize τ hτ m s)=
    OpenLineFrameCoordinates318.frame (Power τ hτ m) (candidateChart τ hτ j)
      (powerFrame τ hτ m j) (candidateChart τ hτ j) le_rfl (regularCoefficient τ hτ m s j) :=
  FramedLineCoefficientGluing318.global_restrict _ _ _ _ _ _ j

lemma element_algebraize (s : homogeneous τ hτ (3*m)) (j : Label 3) :
    element τ hτ m (algebraize τ hτ m s) j=
      PELOriginalWholePowerRegularization318.linear τ hτ m j s := by
  change coefficientEquiv τ hτ j (coefficient τ hτ m (algebraize τ hτ m s) j)=_
  rw [coefficient,algebraize_restrict,LinearEquiv.symm_apply_apply]
  exact (coefficientEquiv τ hτ j).apply_symm_apply _

/-- A single full chart regularization is faithful on the ENTIRE
original section space. This uses its literal section-field fraction. -/
lemma regularization_injective (j : Label 3) :
    Function.Injective (PELOriginalWholePowerRegularization318.linear τ hτ m j) := by
  intro s t h
  have he := congrArg (PELOriginalChartSectionField318.embedding τ hτ j) h
  rw [PELOriginalWholePowerSectionField318.embedding_linear,
    PELOriginalWholePowerSectionField318.embedding_linear] at he
  have hj : algebraMap (PELOriginalGradedSectionRing318.Ring τ hτ)
      (PELOriginalChartSectionField318.SectionField τ hτ)
      (PELOriginalCubicRelationIdeal318.generators τ hτ j)≠0 := by
    simpa only [PELOriginalChartSectionField318.quotientIntoField_mk,
      PELOriginalCubicRelationIdeal318.variable_image] using
      PELOriginalChartSectionField318.denominator_nonzero τ hτ j
  have hnum := (div_left_inj (pow_ne_zero m hj)).mp he
  apply PELOriginalGradedSectionRing318.include_injective τ hτ (3*m)
  exact (IsFractionRing.injective (PELOriginalGradedSectionRing318.Ring τ hτ)
    (PELOriginalChartSectionField318.SectionField τ hτ)) hnum

/-- First inverse: no original full holomorphic sections are lost. -/
theorem recover_algebraize (s : homogeneous τ hτ (3*m)) :
    recover τ hτ m (algebraize τ hτ m s)=s := by
  apply regularization_injective τ hτ m (0 : Label 3)
  rw [regularization_recover,element_algebraize]

/-- Second inverse: EVERY algebraic global section of the actual
whole power sheaf is recovered, including at all former boundary opens. -/
theorem algebraize_recover (s : Γ(Power τ hτ m,⊤)) :
    algebraize τ hτ m (recover τ hτ m s)=s := by
  apply elements_injective τ hτ m
  funext j
  rw [element_algebraize,regularization_recover]

/-- Genuine both-inverse full section comparison, for every m including0.
This is proved from regular functions and sheaf descent, not GAGA. -/
@[expose] def equivalence : homogeneous τ hτ (3*m) ≃ Γ(Power τ hτ m,⊤) where
  toFun := algebraize τ hτ m
  invFun := recover τ hτ m
  left_inv := recover_algebraize τ hτ m
  right_inv := algebraize_recover τ hτ m

lemma element_add (s t : Γ(Power τ hτ m,⊤)) (j : Label 3) :
    element τ hτ m (s+t) j=element τ hτ m s j+element τ hτ m t j := by
  simp only [element,coefficient,map_add]

lemma algebraize_add (s t : homogeneous τ hτ (3*m)) :
    algebraize τ hτ m (s+t)=algebraize τ hτ m s+algebraize τ hτ m t := by
  apply elements_injective τ hτ m
  funext j
  rw [element_algebraize,element_add,element_algebraize,element_algebraize,map_add]

/-- Additive full-section equivalence on the actual global module
sections. Complex linearity requires the actual structural scalar action
and is not silently assigned by transporting this equivalence. -/
@[expose] def additiveEquiv : homogeneous τ hτ (3*m) ≃+ Γ(Power τ hτ m,⊤) :=
  { equivalence τ hτ m with map_add' := algebraize_add τ hτ m }
end PELOriginalWholeSectionEquivalence318
