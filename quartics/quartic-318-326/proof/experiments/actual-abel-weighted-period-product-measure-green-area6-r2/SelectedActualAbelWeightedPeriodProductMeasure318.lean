module

public import SelectedActualAbelExactPeriodProductArea318
public import SelectedActualAbelOrdinaryChartDensity318
public import SelectedActualAbelFiniteProductDensity318

public section

noncomputable section

open Matrix MeasureTheory MeasureTheory.Measure Set UpperHalfPlane
open scoped ENNReal NNReal BigOperators
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedOriginalAbelMeasuredCover318 SelectedActualAbelExactPeriodProductArea318
open SelectedActualAbelOrdinaryChartDensity318 SelectedActualAbelFiniteProductDensity318

namespace SelectedActualAbelWeightedPeriodProductMeasure318

private theorem withDensity_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (q : X → Y) (hq : Measurable q) (μ : Measure X) (w : Y → ℝ≥0∞) (hw : Measurable w) :
    (μ.map q).withDensity w = (μ.withDensity (fun x => w (q x))).map q := by
  ext1 U hU
  rw [withDensity_apply _ hU, Measure.restrict_map hq hU, lintegral_map hw hq,
    Measure.map_apply hq hU, withDensity_apply _ (hq hU)]

/-- The Euclidean measure obtained by the actual inclusion ℍ→ℂ, before hyperbolic weighting. -/
def flatH : Measure UpperHalfPlane := (volume : Measure ℂ).comap UpperHalfPlane.coe

def hyperbolicWeight (τ : UpperHalfPlane) : ℝ≥0∞ :=
  (((1 / NNReal.mk τ.im τ.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ≥0∞)

theorem hyp_weight_measurable : Measurable hyperbolicWeight := by
  have hIm : Continuous (fun τ : UpperHalfPlane => NNReal.mk τ.im τ.im_pos.le) :=
    UpperHalfPlane.continuous_im.subtype_mk _
  have h : Continuous (fun τ : UpperHalfPlane => (1 / NNReal.mk τ.im τ.im_pos.le : ℝ≥0) ^ 2) :=
    (continuous_const.div₀ hIm (fun x => NNReal.ne_iff.mp x.im_ne_zero)).fun_pow 2
  exact h.measurable.coe_nnreal_ennreal

private theorem flat_weight_eq_volume :
    (flatH.withDensity hyperbolicWeight : Measure UpperHalfPlane) = volume := by
  unfold flatH hyperbolicWeight
  exact UpperHalfPlane.volume_def.symm

private theorem exact_weights_compose {M g : ℕ}
    (f : Fin g → Form M) (τ : Fin g → UpperHalfPlane) :
    (∏ i, hyperbolicWeight (τ i)) *
      (positiveDensity f (fun i => quotientMap M (τ i)) : ℝ≥0∞) =
        ENNReal.ofReal (Complex.normSq (periodMatrix f τ).det) := by
  have hfin : (∏ i, hyperbolicWeight (τ i)) < ⊤ :=
    ENNReal.prod_lt_top (fun i _ => ENNReal.coe_lt_top)
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.mul_lt_top hfin ENNReal.coe_lt_top).ne ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (Complex.normSq_nonneg _), mul_comm]
  simpa only [hyperbolicWeight, ENNReal.coe_toReal, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_mk] using original_density_cancels_hyperbolic_weight f τ

/-- On the existing canonical quotient product area, the actual positive Abel density
on an injective ordered period rectangle is the pushforward of the Euclidean
determinant weight, with no independent choice of chart measures. -/
theorem actual_weighted_period_product_measure {M g : ℕ} (hM : 5 ≤ M)
    (f : Fin g → Form M) (B : Fin g → Set UpperHalfPlane)
    (hB : ∀ i, IsOpen (B i)) (hBI : ∀ i, InjOn (quotientMap M) (B i)) :
    (pullbackVolume f hM).restrict (Set.univ.pi fun i => quotientMap M '' B i) =
      (((Measure.pi (fun _ : Fin g => flatH)).withDensity (fun τ =>
         ENNReal.ofReal (Complex.normSq (periodMatrix f τ).det))).restrict
          (Set.univ.pi B)).map (fun τ i => quotientMap M (τ i)) := by
  let q₁ : UpperHalfPlane → Base (image M) := quotientMap M
  let q : (Fin g → UpperHalfPlane) → Domain M g := fun τ i => q₁ (τ i)
  let U : Set (Domain M g) := Set.univ.pi fun i => q₁ '' B i
  let V : Set (Fin g → UpperHalfPlane) := Set.univ.pi B
  let w : Domain M g → ℝ≥0∞ := fun z => (positiveDensity f z : ℝ≥0∞)
  let μ : Measure (Fin g → UpperHalfPlane) :=
    Measure.pi (fun _ : Fin g => (volume : Measure UpperHalfPlane))
  let λ₀ : Measure (Fin g → UpperHalfPlane) := Measure.pi (fun _ : Fin g => flatH)
  let h : (Fin g → UpperHalfPlane) → ℝ≥0∞ := fun τ => ∏ i, hyperbolicWeight (τ i)
  have hq₁ : Measurable q₁ :=
    measurable_quotient_mk' (s := MulAction.orbitRel (image M) UpperHalfPlane)
  have hq : Measurable q :=
    measurable_pi_iff.mpr (fun i => hq₁.comp (measurable_pi_apply i))
  have hw : Measurable w := (positiveDensity_measurable f).coe_nnreal_ennreal
  have hh : Measurable h := Finset.measurable_fun_prod _
    (fun i _ => hyp_weight_measurable.comp (measurable_pi_apply i))
  have hV : MeasurableSet V := MeasurableSet.univ_pi fun i => (hB i).measurableSet
  have hU : MeasurableSet U := by
    apply MeasurableSet.univ_pi
    intro i
    let qp := GammaOneAtlas318.quotient_localHomeomorph M hM
    exact measurableSet_quotient.mpr
      (qp.continuous.isOpen_preimage _ (qp.isOpenMap _ (hB i))).measurableSet
  have hA : (productArea (g := g) hM).restrict U = (μ.restrict V).map q :=
    exact_ordered_period_product_area M hM B hB hBI
  letI : SigmaFinite flatH := by unfold flatH; infer_instance
  letI : SigmaFinite (flatH.withDensity hyperbolicWeight) := by
    rw [flat_weight_eq_volume]
    infer_instance
  have hμ : μ = λ₀.withDensity h := by
    have hp := pi_withDensity_coordinate_prod g (fun _ => flatH)
      (fun _ => hyperbolicWeight) (fun _ => hyp_weight_measurable)
    change Measure.pi (fun _ : Fin g => flatH.withDensity hyperbolicWeight) =
      λ₀.withDensity h at hp
    simpa only [flat_weight_eq_volume] using hp
  change ((productArea (g := g) hM).withDensity w).restrict U = _
  rw [restrict_withDensity hU, hA, withDensity_map q hq _ w hw, hμ,
    restrict_withDensity hV, ← withDensity_mul (λ₀.restrict V) hh (hw.comp hq)]
  have hrow : h * (fun τ => w (q τ)) =
      fun τ => ENNReal.ofReal (Complex.normSq (periodMatrix f τ).det) := by
    funext τ
    exact exact_weights_compose f τ
  rw [hrow, ← restrict_withDensity hV]

end SelectedActualAbelWeightedPeriodProductMeasure318

#print axioms SelectedActualAbelWeightedPeriodProductMeasure318.actual_weighted_period_product_measure
