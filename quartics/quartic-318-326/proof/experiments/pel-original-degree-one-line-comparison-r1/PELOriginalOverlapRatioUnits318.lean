module
public import PELOriginalChartOverlapMorphism318
public import GlobalScalarSheafEndomorphism318
public import PELOriginalAlgebraicHyperplaneImage318
public section
noncomputable section
namespace PELOriginalOverlapRatioUnits318
open AlgebraicGeometry CategoryTheory
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalChartAnalyticEvaluation318 PELOriginalChartOverlapLocalization318
variable (τ : ℂ) (hτ : 0 < τ.im) (j k : Label 3)

/-- Exact linear hyperplane transition in the literal whole intersection
ring, distinct from the quadratic transition used for sextic sections. -/
theorem ratio_transition (i : Label 3) :
    algebraMap (CoordinateChart τ hτ j) (Overlap τ hτ j k) (ratioElement τ hτ j i) =
      fromOther τ hτ j k (ratioElement τ hτ k i) *
        algebraMap (CoordinateChart τ hτ j) (Overlap τ hτ j k) (ratioElement τ hτ j k) := by
  rw [fromOther_ratio,chartRatios,mul_assoc]
  rw [mul_comm (IsLocalization.Away.invSelf (ratioElement τ hτ j k)),
    IsLocalization.Away.mul_invSelf,mul_one]

@[expose] def transitionSection :
    Γ(Spec (CommRingCat.of (Overlap τ hτ j k)),⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Overlap τ hτ j k))).inv
    (algebraMap (CoordinateChart τ hτ j) (Overlap τ hτ j k) (ratioElement τ hτ j k))

lemma transitionSection_isUnit : IsUnit (transitionSection τ hτ j k) :=
  (IsLocalization.Away.algebraMap_isUnit (ratioElement τ hτ j k)).map
    (Scheme.ΓSpecIso (CommRingCat.of (Overlap τ hτ j k))).inv

/-- The actual ratio acts invertibly on the structure module sheaf of
the genuine scheme intersection. This fixes the linear O(1) transition. -/
@[expose] def transitionIso :
    SheafOfModules.unit (Spec (CommRingCat.of (Overlap τ hτ j k))).ringCatSheaf ≅
      SheafOfModules.unit (Spec (CommRingCat.of (Overlap τ hτ j k))).ringCatSheaf :=
  GlobalScalarSheafEndomorphism318.unitIso _ (transitionSection_isUnit τ hτ j k).unit

lemma transitionIso_hom : (transitionIso τ hτ j k).hom =
    GlobalScalarSheafEndomorphism318.endomorphism _ (transitionSection τ hτ j k) := by
  change GlobalScalarSheafEndomorphism318.endomorphism _
    (transitionSection_isUnit τ hτ j k).unit.val = _
  rw [IsUnit.unit_spec]

lemma left_ratios (i : Label 3) :
    (PELOriginalChartOverlapMorphism318.left τ hτ j k).appTop
      (PELOriginalAlgebraicHyperplaneImage318.ratios τ hτ j i) =
    (Scheme.ΓSpecIso (CommRingCat.of (Overlap τ hτ j k))).inv
      (algebraMap (CoordinateChart τ hτ j) (Overlap τ hτ j k) (ratioElement τ hτ j i)) := by
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap (CoordinateChart τ hτ j) (Overlap τ hτ j k))))
      (ratioElement τ hτ j i)).symm

lemma right_ratios (i : Label 3) :
    (PELOriginalChartOverlapMorphism318.right τ hτ j k).appTop
      (PELOriginalAlgebraicHyperplaneImage318.ratios τ hτ k i) =
    (Scheme.ΓSpecIso (CommRingCat.of (Overlap τ hτ j k))).inv
      (fromOther τ hτ j k (ratioElement τ hτ k i)) := by
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (fromOther τ hτ j k).toRingHom))
      (ratioElement τ hτ k i)).symm

/-- Equality of genuine regular functions on the actual scheme
intersection, with the exact original linear transition unit. -/
theorem section_transition (i : Label 3) :
    (PELOriginalChartOverlapMorphism318.left τ hτ j k).appTop
      (PELOriginalAlgebraicHyperplaneImage318.ratios τ hτ j i) =
    (PELOriginalChartOverlapMorphism318.right τ hτ j k).appTop
      (PELOriginalAlgebraicHyperplaneImage318.ratios τ hτ k i) *
        transitionSection τ hτ j k := by
  rw [left_ratios,right_ratios,transitionSection,←map_mul,ratio_transition]
end PELOriginalOverlapRatioUnits318
