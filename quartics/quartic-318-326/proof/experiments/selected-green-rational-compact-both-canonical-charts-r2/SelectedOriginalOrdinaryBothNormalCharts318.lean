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
variable (hQ : IsField (genericRoot M p)) (hp : p.Monic)
variable (hu : IsUnit (AdjoinRoot.mk p p.derivative))

local notation "K" => genericRoot M p
local notation "QS" => ordinaryRoot M p
local notation "X" => compact M p hQ

local instance : Field K := hQ.toField
local instance : Algebra ℚ JField := RatFunc.instAlgebraOfPolynomial ℚ ℚ
local instance : Algebra JField K := chartJAlgebra M p
local instance : Algebra ℚ K := rationalAlgebra M p
local instance : IsScalarTower ℚ JField K := chartTower M p

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

theorem ordinary_lands (i : Fin 2) :
    Set.range (ordinaryEmbedding M p hQ hp hu) ⊆ Set.range (chartEmbedding K i) := by
  have ho := ordinaryEmbedding_range M p hQ hp hu
  have hc := @chartEmbedding_range K hQ.toField (chartJAlgebra M p)
    (rationalAlgebra M p) (chartTower M p) i
  rw [← Scheme.Hom.coe_opensRange,← Scheme.Hom.coe_opensRange,ho,hc]
  exact (compactJ M p hQ).preimage_mono (baseOrdinary_le i)

/-- The actual ordinary map factors uniquely through each of the two
affine charts of the same rational compact normalization. -/
@[expose] def chartFactor (i : Fin 2) :
    Spec (CommRingCat.of QS) ⟶ Spec (CommRingCat.of (Order K i)) :=
  IsOpenImmersion.lift (chartEmbedding K i) (ordinaryEmbedding M p hQ hp hu)
    (by exact ordinary_lands M p hQ hp hu i)

theorem chartFactor_fac (i : Fin 2) :
    chartFactor M p hQ hp hu i ≫ chartEmbedding K i = ordinaryEmbedding M p hQ hp hu :=
  IsOpenImmersion.lift_fac _ _ _

/-- Ring hom of the genuine chart factor, not a new coefficient
choice. It is characterized both by the open square and the literal
restriction to the entire common generic field. -/
@[expose] def intoOrdinary (i : Fin 2) : Order K i →+* QS :=
  (Scheme.Spec.preimage (chartFactor M p hQ hp hu i)).unop.hom

theorem Spec_intoOrdinary (i : Fin 2) :
    Spec.map (CommRingCat.ofHom (intoOrdinary M p hQ hp hu i)) ≫ chartEmbedding K i =
      ordinaryEmbedding M p hQ hp hu := by
  have h : Spec.map (CommRingCat.ofHom (intoOrdinary M p hQ hp hu i)) =
      chartFactor M p hQ hp hu i := Scheme.Spec.map_preimage _
  rw [h,chartFactor_fac]

theorem intoOrdinary_at_generic (i : Fin 2) :
    (SelectedOriginalRationalOrdinaryIntegral318.genericEmbedding M p).comp
      (intoOrdinary M p hQ hp hu i) = orderVal K i := by
  have h : Spec.map (CommRingCat.ofHom
      ((SelectedOriginalRationalOrdinaryIntegral318.genericEmbedding M p).comp
        (intoOrdinary M p hQ hp hu i))) ≫ chartEmbedding K i =
      Spec.map (CommRingCat.ofHom (orderVal K i)) ≫ chartEmbedding K i := by
    have he := @chart_original K hQ.toField (chartJAlgebra M p)
      (rationalAlgebra M p) (chartTower M p) i
    rw [he,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc,Spec_intoOrdinary]
    exact ordinary_original M p hQ hp hu
  have h' : CommRingCat.ofHom
      ((SelectedOriginalRationalOrdinaryIntegral318.genericEmbedding M p).comp
        (intoOrdinary M p hQ hp hu i)) = CommRingCat.ofHom (orderVal K i) :=
    Spec.map_injective ((cancel_mono (chartEmbedding K i)).mp h)
  exact congrArg (fun f : CommRingCat.of (Order K i) ⟶ CommRingCat.of K => f.hom) h' 

end SelectedOriginalOrdinaryBothNormalCharts318

#print axioms SelectedOriginalOrdinaryBothNormalCharts318.Spec_intoOrdinary
#print axioms SelectedOriginalOrdinaryBothNormalCharts318.intoOrdinary_at_generic
