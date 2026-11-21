module
public import SelectedOriginalOrdinaryBothNormalCharts318
public import SelectedGreenRationalCompactIntrinsic318
public import SelectedCompactDifferentialSquare318
public import IntrinsicDifferentialFunctor318
public section
noncomputable section

open Polynomial NumberField CategoryTheory AlgebraicGeometry Opposite
open SelectedOriginalOrdinaryBothNormalCharts318 SelectedRationalCompactIntrinsicCoefficient318
open SelectedOriginalRationalOrdinaryRoot318 SelectedOriginalRationalOrdinaryGeometry318
open SelectedOriginalGenericChartClosures318 SelectedOriginalGenericClosureOverlap318
open SelectedOriginalGenericCompactCharts318 SelectedRationalRootCompactInstall318
open SelectedOriginalCompactClassicalDifferentials318 SelectedIntrinsicGlobalToAffine318
open SelectedCompactDifferentialSquare318

namespace SelectedActualRationalCanonicalBothCharts318

variable (M : ℕ) [NeZero M] (p : (OpenJModel318.Base M)[X])
variable (hQ : IsField (genericRoot M p)) (hp : p.Monic)
variable (hu : IsUnit (AdjoinRoot.mk p p.derivative))

local notation "K" => genericRoot M p
local notation "Cpt" => compact M p hQ
local notation "src" => compactStructure M p hQ
local notation "QS" => ordinaryRoot M p
local notation "j" => ordinaryEmbedding M p hQ hp hu

variable (i : Fin 2)
local notation "A" => NormalOrder M p hQ i

@[expose] def chartConst : Algebra ℚ A := by
  letI : Algebra ℚ[X] K := (@polynomial K hQ.toField (chartJAlgebra M p) i).toAlgebra
  exact Algebra.compHom A (algebraMap ℚ ℚ[X])

/-- The actual compact chart is over the original structural Q map.
The proof keeps the literal polynomial ring map into that order. -/
theorem chart_over_Q :
    letI : Algebra ℚ A := chartConst M p hQ i
    normalChart M p hQ i ≫ src = Spec.algebraMap ℚ A := by
  letI : Algebra ℚ A := chartConst M p hQ i
  letI : Algebra ℚ[X] K := (@polynomial K hQ.toField (chartJAlgebra M p) i).toAlgebra
  have hJ : normalChart M p hQ i ≫ compactJ M p hQ =
      Spec.algebraMap ℚ[X] A ≫ JLineAtlas318.chart ℚ i :=
    @chart_over_base K hQ.toField (chartJAlgebra M p) (rationalAlgebra M p) (chartTower M p) i
  change normalChart M p hQ i ≫ (compactJ M p hQ ≫ ProjectiveJLine318.structureMap ℚ) = _
  rw [← Category.assoc,hJ,Category.assoc,JLineAtlas318.chart_over_base]
  have hScalar : (algebraMap ℚ[X] A).comp (algebraMap ℚ ℚ[X]) =
      algebraMap ℚ A := rfl
  have hBundled : CommRingCat.ofHom (algebraMap ℚ ℚ[X]) ≫
      CommRingCat.ofHom (algebraMap ℚ[X] A) = CommRingCat.ofHom (algebraMap ℚ A) :=
    (CommRingCat.ofHom_comp (algebraMap ℚ ℚ[X]) (algebraMap ℚ[X] A)).symm.trans
      (congrArg CommRingCat.ofHom hScalar)
  exact (Spec.map_comp (CommRingCat.ofHom (algebraMap ℚ ℚ[X]))
    (CommRingCat.ofHom (algebraMap ℚ[X] A))).symm.trans (congrArg Spec.map hBundled)

include hp hu in
@[expose] def ordinaryFromChart :
    letI : Algebra ℚ A := chartConst M p hQ i
    A →ₐ[ℚ] QS := by
  letI : Algebra ℚ A := chartConst M p hQ i
  exact {
    toRingHom := intoOrdinary M p hQ hp hu i
    commutes' r := RingHom.map_rat_algebraMap (intoOrdinary M p hQ hp hu i) r }

@[expose] def chartRestriction (w : RationalSections M p hQ) :
    letI : Algebra ℚ A := chartConst M p hQ i
    KaehlerDifferential ℚ A := by
  letI : Algebra ℚ A := chartConst M p hQ i
  letI : IsOpenImmersion (normalChart M p hQ i) := by exact normalChart_open M p hQ i
  exact restrict (normalChart M p hQ i) src (chart_over_Q M p hQ i) w

theorem original_ordinary_over_Q :
    j ≫ src = Spec.algebraMap ℚ QS := by
  letI : Fact p.Monic := ⟨hp⟩
  exact actual_ordinary_Q M p hu hQ

/-- For BOTH actual normalized affine charts, the original ordinary
differential is the algebraic image of the SAME global compact form.
This is the literal affine open square and identity pullback. -/
theorem ordinary_restriction_of_chart (w : RationalSections M p hQ) :
    letI : Algebra ℚ A := chartConst M p hQ i
    restrict j src (original_ordinary_over_Q M p hQ hp hu) w =
      AlgHomDifferential318.map (ordinaryFromChart M p hQ hp hu i)
        (chartRestriction M p hQ i w) := by
  letI : Algebra ℚ A := chartConst M p hQ i
  letI : IsOpenImmersion (normalChart M p hQ i) := normalChart_open M p hQ i
  have hId : (𝟙 Cpt) ≫ src = src := Category.id_comp src
  have hs : j ≫ (𝟙 Cpt) =
      Spec.map (CommRingCat.ofHom (ordinaryFromChart M p hQ hp hu i).toRingHom) ≫
        normalChart M p hQ i :=
    (Category.comp_id j).trans (Spec_intoOrdinary M p hQ hp hu i).symm
  let w' : Γ(FamilyIntrinsicDifferentials318.omega src,⊤) := w
  have h := restrict_square src src (𝟙 Cpt) hId (ordinaryFromChart M p hQ hp hu i) j
    (normalChart M p hQ i) (original_ordinary_over_Q M p hQ hp hu) (chart_over_Q M p hQ i) hs w'
  have hi : IntrinsicDifferentialPullback318.globalSection (𝟙 Cpt) src src hId w' = w' :=
    IntrinsicDifferentialFunctor318.globalSection_id src hId w'
  exact (congrArg (restrict j src (original_ordinary_over_Q M p hQ hp hu)) hi).symm.trans h

/-- The coefficient of the same original canonical differential is
computed from EITHER of the two actual normal affine charts. In
particular the reciprocal-chart representative is not an input to the
construction and uses the same rational function dJ convention. -/
theorem original_canonical_from_both_charts (w : RationalSections M p hQ) :
    letI : Algebra ℚ A := chartConst M p hQ i
    rationalCoefficient M p hp hu hQ w =
      ordinaryFrame M p hp hu
        (AlgHomDifferential318.map (ordinaryFromChart M p hQ hp hu i)
          (chartRestriction M p hQ i w)) := by
  letI : Algebra ℚ A := chartConst M p hQ i
  have hq := original_ordinary_over_Q M p hQ hp hu
  exact (rationalCoefficient_apply M p hp hu hQ hq w).trans
    (congrArg (ordinaryFrame M p hp hu) (ordinary_restriction_of_chart M p hQ hp hu i w))

end SelectedActualRationalCanonicalBothCharts318

#print axioms SelectedActualRationalCanonicalBothCharts318.chart_over_Q
#print axioms SelectedActualRationalCanonicalBothCharts318.ordinary_restriction_of_chart

#print axioms SelectedActualRationalCanonicalBothCharts318.original_canonical_from_both_charts
