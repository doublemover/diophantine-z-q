module
public import SelectedOriginalRationalOrdinaryGeometry318
public import SelectedOriginalCompactOverlapIdentity318
public import Mathlib.AlgebraicGeometry.OpenImmersion
public section
noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open SelectedOriginalRationalOrdinaryRoot318 SelectedOriginalRationalOrdinaryGeometry318
open SelectedOriginalGenericChartClosures318 SelectedOriginalGenericCompactNormal318
open SelectedOriginalGenericClosureOverlap318 SelectedOriginalGenericCompactCharts318
open SelectedOriginalCompactOverlapIdentity318 SelectedRationalRootCompactInstall318

namespace SelectedOriginalOrdinaryBothNormalCharts318

variable (M : ℕ) [NeZero M] (p : (OpenJModel318.Base M)[X])
variable (hQ : IsField (genericRoot M p))

local notation "K" => genericRoot M p
local notation "QS" => ordinaryRoot M p

/-- The exact dictionary used by the hosted-green one-chart construction
is installed explicitly, separately for each of the two chart indices. -/
abbrev NormalOrder (i : Fin 2) :=
  @Order K hQ.toField (chartJAlgebra M p) i

abbrev normalChart (i : Fin 2) :
    Spec (CommRingCat.of (NormalOrder M p hQ i)) ⟶ compact M p hQ :=
  @chartEmbedding K hQ.toField (chartJAlgebra M p) (rationalAlgebra M p) (chartTower M p) i

theorem normalChart_open (i : Fin 2) : IsOpenImmersion (normalChart M p hQ i) := by
  letI : Field K := hQ.toField
  letI : Algebra JField K := chartJAlgebra M p
  let f := Spec.map (CommRingCat.ofHom
    (@SelectedOriginalGenericCompactCharts318.actualSections K hQ.toField
      (chartJAlgebra M p) (rationalAlgebra M p) (chartTower M p) i).toRingHom)
  let g := (sourceCover K i).2.fromSpec
  letI : IsIso f := @SelectedOriginalGenericCompactCharts318.chartSpec_isIso K hQ.toField
    (chartJAlgebra M p) (rationalAlgebra M p) (chartTower M p) i
  change IsOpenImmersion (f ≫ g)
  exact @IsOpenImmersion.comp _ _ _ f g (IsOpenImmersion.of_isIso f)
    (sourceCover K i).2.isOpenImmersion_fromSpec

/-- The actual normal order included in the original whole generic field. -/
abbrev normalOrderVal (i : Fin 2) : NormalOrder M p hQ i →+* K :=
  @orderVal K hQ.toField (chartJAlgebra M p) i

/-- The literal J(J−1728) ordinary open lands in both actual
projective affine charts: it avoids J=0 and ∞. -/
theorem baseOrdinary_le (i : Fin 2) : baseOrdinary ≤ (targetCover i).1 := by
  fin_cases i
  · have hin : PrimeSpectrum.basicOpen SelectedOriginalRationalOrdinary318.denominator ≤
        (JLineAtlas318.chart ℚ 1)⁻¹ᵁ (targetCover 0).1 := by
      have hz : (JLineAtlas318.chart ℚ 1)⁻¹ᵁ (targetCover 0).1 =
          PrimeSpectrum.basicOpen (Polynomial.X : ℚ[X]) := target_other_preimage 1
      rw [hz,SelectedOriginalRationalOrdinary318.denominator,PrimeSpectrum.basicOpen_mul]
      exact inf_le_left
    exact ((JLineAtlas318.chart ℚ 1).image_mono hin).trans (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_le_right)
  · exact (JLineAtlas318.chart ℚ 1).image_mono le_top

variable (hp : p.Monic) (hu : IsUnit (AdjoinRoot.mk p p.derivative))

theorem ordinary_lands (i : Fin 2) :
    Set.range (ordinaryEmbedding M p hQ hp hu) ⊆ Set.range (normalChart M p hQ i) := by
  letI : IsOpenImmersion (normalChart M p hQ i) := normalChart_open M p hQ i
  have ho := ordinaryEmbedding_range M p hQ hp hu
  have hc : (normalChart M p hQ i).opensRange = (compactJ M p hQ)⁻¹ᵁ (targetCover i).1 :=
    @chartEmbedding_range K hQ.toField (chartJAlgebra M p)
      (rationalAlgebra M p) (chartTower M p) i
  rw [← Scheme.Hom.coe_opensRange,← Scheme.Hom.coe_opensRange,ho,hc]
  exact (compactJ M p hQ).preimage_mono (baseOrdinary_le i)

include hp hu in
/-- The actual ordinary map factors uniquely through each of the two
affine charts of the same rational compact normalization. -/
@[expose] def chartFactor (i : Fin 2) :
    Spec (CommRingCat.of QS) ⟶ Spec (CommRingCat.of (NormalOrder M p hQ i)) := by
  letI : IsOpenImmersion (normalChart M p hQ i) := by exact normalChart_open M p hQ i
  exact IsOpenImmersion.lift (normalChart M p hQ i) (ordinaryEmbedding M p hQ hp hu)
    (ordinary_lands M p hQ hp hu i)

theorem chartFactor_fac (i : Fin 2) :
    chartFactor M p hQ hp hu i ≫ normalChart M p hQ i = ordinaryEmbedding M p hQ hp hu := by
  letI : IsOpenImmersion (normalChart M p hQ i) := normalChart_open M p hQ i
  unfold chartFactor
  exact IsOpenImmersion.lift_fac _ _ _

include hp hu in
/-- Ring hom of the genuine chart factor, not a new coefficient
choice. It is characterized both by the open square and the literal
restriction to the entire common generic field. -/
@[expose] def intoOrdinary (i : Fin 2) : NormalOrder M p hQ i →+* QS :=
  (Scheme.Spec.preimage (chartFactor M p hQ hp hu i)).unop.hom

theorem Spec_intoOrdinary (i : Fin 2) :
    Spec.map (CommRingCat.ofHom (intoOrdinary M p hQ hp hu i)) ≫ normalChart M p hQ i =
      ordinaryEmbedding M p hQ hp hu := by
  have h : Spec.map (CommRingCat.ofHom (intoOrdinary M p hQ hp hu i)) =
      chartFactor M p hQ hp hu i := Scheme.Spec.map_preimage _
  exact (congrArg (fun g : Spec (CommRingCat.of QS) ⟶
    Spec (CommRingCat.of (NormalOrder M p hQ i)) => g ≫ normalChart M p hQ i) h).trans
      (chartFactor_fac M p hQ hp hu i)

theorem intoOrdinary_at_generic (i : Fin 2) :
    (SelectedOriginalRationalOrdinaryIntegral318.genericEmbedding M p).comp
      (intoOrdinary M p hQ hp hu i) = normalOrderVal M p hQ i := by
  letI : IsOpenImmersion (normalChart M p hQ i) := normalChart_open M p hQ i
  have h : Spec.map (CommRingCat.ofHom
      ((SelectedOriginalRationalOrdinaryIntegral318.genericEmbedding M p).comp
        (intoOrdinary M p hQ hp hu i))) ≫ normalChart M p hQ i =
      Spec.map (CommRingCat.ofHom (normalOrderVal M p hQ i)) ≫ normalChart M p hQ i := by
    have he : Spec.map (CommRingCat.ofHom (normalOrderVal M p hQ i)) ≫ normalChart M p hQ i =
        (@genericMap K hQ.toField (chartJAlgebra M p)).toNormalization :=
      @chart_original K hQ.toField (chartJAlgebra M p)
        (rationalAlgebra M p) (chartTower M p) i
    rw [he,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc,Spec_intoOrdinary]
    exact ordinary_original M p hQ hp hu
  have h' : CommRingCat.ofHom
      ((SelectedOriginalRationalOrdinaryIntegral318.genericEmbedding M p).comp
        (intoOrdinary M p hQ hp hu i)) = CommRingCat.ofHom (normalOrderVal M p hQ i) :=
    Spec.map_injective ((cancel_mono (normalChart M p hQ i)).mp h)
  exact congrArg (fun f : CommRingCat.of (NormalOrder M p hQ i) ⟶ CommRingCat.of K => f.hom) h'

end SelectedOriginalOrdinaryBothNormalCharts318

#print axioms SelectedOriginalOrdinaryBothNormalCharts318.Spec_intoOrdinary
#print axioms SelectedOriginalOrdinaryBothNormalCharts318.intoOrdinary_at_generic
