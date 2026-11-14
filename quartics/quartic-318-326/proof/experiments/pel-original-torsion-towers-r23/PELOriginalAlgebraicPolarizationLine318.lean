module
public import PELOriginalMixedRatioCover318
public import IntegralRatioImageFrame318
public import IntegralOpenIntersection318
public import IntrinsicLineDifference318
public section
noncomputable section
namespace PELOriginalAlgebraicPolarizationLine318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalLevelTheta318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateIntegral : IsIntegral (candidate τ hτ) :=
  PELOriginalCandidateIntegral318.integral τ hτ

/-- An actual nonempty common rational anchor, produced from the full
scheme cover rather than imposed as a simultaneous theta nonvanishing
assumption. -/
@[expose] def anchor : NonemptyIndex τ hτ :=
  ⟨Classical.choose (exists_anchor τ hτ),Classical.choose_spec (exists_anchor τ hτ)⟩

abbrev opens (a : NonemptyIndex τ hτ) := mixedOpen τ hτ a.val
local instance openNonempty (a : NonemptyIndex τ hτ) : Nonempty (opens τ hτ a).toScheme := a.property
local instance openIntegral (a : NonemptyIndex τ hτ) : IsIntegral (opens τ hτ a).toScheme :=
  isIntegral_of_isOpenImmersion (opens τ hτ a).ι
local instance overlapNonempty (a b : NonemptyIndex τ hτ) :
    Nonempty (overlap τ hτ a.val b.val).toScheme := intersection_nonempty τ hτ a b

lemma coversTop : (⊤ : (candidate τ hτ).Opens) ≤ ⨆ a : NonemptyIndex τ hτ,opens τ hτ a := by
  intro x hx
  obtain ⟨a,ha⟩ := nonempty_covers τ hτ x
  exact le_iSup (opens τ hτ) a ha

/-- The actual degree-three image sheaf on the SAME candidate, using
literal regular cubic ratios on the produced common anchor. -/
@[expose] def cubicSheaf : (candidate τ hτ).Modules :=
  ChartGeneratedImageSheaf318.sheaf (opens τ hτ (anchor τ hτ)).ι
    (cubic τ hτ (anchor τ hτ).val)

/-- The actual degree-two image sheaf. Its ratios come from the genuine
regular theta2 scheme morphism, not from an analytic map declared regular. -/
@[expose] def quadraticSheaf : (candidate τ hτ).Modules :=
  ChartGeneratedImageSheaf318.sheaf (opens τ hτ (anchor τ hτ)).ι
    (quadratic τ hτ (anchor τ hτ).val)

@[expose] def cubicFrame (b : NonemptyIndex τ hτ) :
    SheafOfModules.unit (opens τ hτ b).toScheme.ringCatSheaf ≅
      (cubicSheaf τ hτ).restrict (opens τ hτ b).ι :=
  IntegralRatioImageFrame318.frame
    (toRight τ hτ (anchor τ hτ).val b.val) (toLeft τ hτ (anchor τ hτ).val b.val)
    (opens τ hτ b).ι (opens τ hτ (anchor τ hτ)).ι
    (IntegralOpenIntersection318.cartesian _ _)
    (cubic τ hτ (anchor τ hτ).val) (cubic τ hτ b.val)
    (cubic_unit τ hτ (anchor τ hτ).val b.val).unit
    (fun i => by rw [IsUnit.unit_spec]; exact cubic_transition τ hτ _ _ i)
    b.val.1 (cubic_self τ hτ b.val)

@[expose] def quadraticFrame (b : NonemptyIndex τ hτ) :
    SheafOfModules.unit (opens τ hτ b).toScheme.ringCatSheaf ≅
      (quadraticSheaf τ hτ).restrict (opens τ hτ b).ι :=
  IntegralRatioImageFrame318.frame
    (toRight τ hτ (anchor τ hτ).val b.val) (toLeft τ hτ (anchor τ hτ).val b.val)
    (opens τ hτ b).ι (opens τ hτ (anchor τ hτ)).ι
    (IntegralOpenIntersection318.cartesian _ _)
    (quadratic τ hτ (anchor τ hτ).val) (quadratic τ hτ b.val)
    (quadratic_unit τ hτ (anchor τ hτ).val b.val).unit
    (fun i => by rw [IsUnit.unit_spec]; exact quadratic_transition τ hτ _ _ i)
    b.val.2 (quadratic_self τ hτ b.val)

@[expose] def cubicLine : LineSheafClass318.Line (candidate τ hτ) :=
  ⟨cubicSheaf τ hτ,NonemptyIndex τ hτ,opens τ hτ,coversTop τ hτ,cubicFrame τ hτ⟩
@[expose] def quadraticLine : LineSheafClass318.Line (candidate τ hτ) :=
  ⟨quadraticSheaf τ hτ,NonemptyIndex τ hτ,opens τ hτ,coversTop τ hτ,quadraticFrame τ hτ⟩

/-- A concrete algebraic candidate for the original degree-one line:
the TRUE intrinsic tensor of the degree-three sheaf with the TRUE
inverse of the degree-two sheaf. No root in a Picard group is assumed. -/
@[expose] def line : LineSheafClass318.Line (candidate τ hτ) :=
  IntrinsicLineDifference318.line (cubicSheaf τ hτ) (quadraticSheaf τ hτ)
    (opens τ hτ) (coversTop τ hτ) (cubicFrame τ hτ) (quadraticFrame τ hτ)

abbrev sheaf := (line τ hτ).object

/-- Genuine local freeness on the entire original candidate scheme,
including all former denominator boundaries and nonclosed primes. -/
theorem locallyFree : (sheaf τ hτ).IsLocallyFree :=
  IntrinsicLineDifference318.locallyFree _ _ _ (coversTop τ hτ) _ _

/-- An actual tensor isomorphism recovers the unchanged cubic sheaf.
This is stronger than a relation imposed on line-class labels. -/
@[expose] def tensorQuadraticIso :
    IntrinsicTensorSheaf318.tensor (sheaf τ hτ) (quadraticSheaf τ hτ) ≅ cubicSheaf τ hτ :=
  IntrinsicLineDifference318.cancellation _ _ _ (coversTop τ hτ) _ _

/-- The exact regular unit cocycle of the constructed algebraic line is
the cubic cocycle divided by the quadratic cocycle on every FULL
scheme intersection. The analytic original comparison is a separate
consumer of these already-existing algebraic frames. -/
theorem transition (a b : NonemptyIndex τ hτ) :
    (LineFrameCocycle318.cocycle (sheaf τ hτ) (opens τ hτ) (line τ hτ).frame).transition a b =
      (LineFrameCocycle318.cocycle (cubicSheaf τ hτ) (opens τ hτ) (cubicFrame τ hτ)).transition a b *
        ((LineFrameCocycle318.cocycle (quadraticSheaf τ hτ) (opens τ hτ)
          (quadraticFrame τ hτ)).transition a b)⁻¹ :=
  IntrinsicLineDifference318.transition _ _ _ _ _ _ _

@[expose] def cubicSection (i : Label 3) :
    SheafOfModules.unit (candidate τ hτ).ringCatSheaf ⟶ cubicSheaf τ hτ :=
  SheafOfModules.ιFree i ≫ factorThruImage (ChartGeneratedImageSheaf318.presentation
    (opens τ hτ (anchor τ hτ)).ι (cubic τ hτ (anchor τ hτ).val))
@[expose] def quadraticSection (i : Label 2) :
    SheafOfModules.unit (candidate τ hτ).ringCatSheaf ⟶ quadraticSheaf τ hτ :=
  SheafOfModules.ιFree i ≫ factorThruImage (ChartGeneratedImageSheaf318.presentation
    (opens τ hτ (anchor τ hτ)).ι (quadratic τ hτ (anchor τ hτ).val))

/-- Every original cubic coordinate section has its exact regular
coefficient in the actual mixed-chart frame. -/
theorem cubic_section_coefficient (a : NonemptyIndex τ hτ) (i : Label 3) :
    (Scheme.Modules.restrictUnitIso (opens τ hτ a).ι).inv ≫
      (Scheme.Modules.restrictFunctor (opens τ hτ a).ι).map (cubicSection τ hτ i) =
    GlobalScalarSheafEndomorphism318.endomorphism _ (cubic τ hτ a.val i) ≫
      (cubicFrame τ hτ a).hom :=
  IntegralRatioImageFrame318.section_in_frame _ _ _ _ _ _ _ _ _ _ _ _

/-- The corresponding exact degree-two coefficients fix the actual
inverse-line normalization rather than an unspecified analytic gauge. -/
theorem quadratic_section_coefficient (a : NonemptyIndex τ hτ) (i : Label 2) :
    (Scheme.Modules.restrictUnitIso (opens τ hτ a).ι).inv ≫
      (Scheme.Modules.restrictFunctor (opens τ hτ a).ι).map (quadraticSection τ hτ i) =
    GlobalScalarSheafEndomorphism318.endomorphism _ (quadratic τ hτ a.val i) ≫
      (quadraticFrame τ hτ a).hom :=
  IntegralRatioImageFrame318.section_in_frame _ _ _ _ _ _ _ _ _ _ _ _
end PELOriginalAlgebraicPolarizationLine318
