module

public import SelectedActualAbelExactPeriodSheetArea318
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Comap

public section

noncomputable section

open Function Set MeasureTheory UpperHalfPlane
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedGammaOneQuotientArea318 SelectedActualAbelExactPeriodSheetArea318
open scoped ENNReal NNReal

namespace SelectedActualGammaOneAreaFullSupport318

private theorem upper_half_plane_open_pos (U : Set UpperHalfPlane)
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < (volume : Measure UpperHalfPlane) U := by
  let μ : Measure UpperHalfPlane := (volume : Measure ℂ).comap UpperHalfPlane.coe
  let w (t : UpperHalfPlane) : ℝ≥0∞ :=
    (((1 / NNReal.mk t.im t.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ≥0∞)
  have hIm : Continuous (fun t : UpperHalfPlane => NNReal.mk t.im t.im_pos.le) :=
    UpperHalfPlane.continuous_im.subtype_mk _
  have hnn (t : UpperHalfPlane) : NNReal.mk t.im t.im_pos.le ≠ 0 :=
    NNReal.ne_iff.mp t.im_ne_zero
  have hw : Measurable w := by
    have hc : Continuous (fun t : UpperHalfPlane =>
        (1 / NNReal.mk t.im t.im_pos.le : ℝ≥0) ^ 2) :=
      (continuous_const.div₀ hIm hnn).fun_pow 2
    exact hc.measurable.coe_nnreal_ennreal
  have hw0 (t : UpperHalfPlane) : w t ≠ 0 := by
    have hz : (1 / NNReal.mk t.im t.im_pos.le : ℝ≥0) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (div_ne_zero one_ne_zero (hnn t))
    exact_mod_cast hz
  have hμ : μ U = (volume : Measure ℂ) (UpperHalfPlane.coe '' U) :=
    Measure.comap_apply UpperHalfPlane.coe measurableEmbedding_coe.injective
      (fun S hS => measurableEmbedding_coe.measurableSet_image.mpr hS)
      (volume : Measure ℂ) hU.measurableSet
  have ho : IsOpen (UpperHalfPlane.coe '' U) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hU
  have hpos : 0 < μ U := by
    rw [hμ]
    exact ho.measure_pos _ (hne.image _)
  change 0 < μ.withDensity w U
  apply pos_iff_ne_zero.mpr
  intro hz
  have hzz := (withDensity_apply_eq_zero (μ := μ) (s := U) hw).mp hz
  have ht : ({t : UpperHalfPlane | w t ≠ 0} ∩ U) = U := by
    ext t
    exact ⟨fun h => h.2,fun h => ⟨hw0 t,h⟩⟩
  rw [ht] at hzz
  exact hpos.ne' hzz

/-- The canonical, already constructed fine-level quotient measure has
full support. The positive mass is computed by an actual injective
period sheet inside the given open, using exactly the same hyperbolic
density, and not a newly normalized measure. -/
theorem actual_area_open_positive (M : ℕ) (hM : 5 ≤ M) :
    Measure.IsOpenPosMeasure (area M hM) := by
  constructor
  intro U hU hUne
  obtain ⟨u,hu⟩ := hUne
  let q := quotientMap M
  have hqLoc := GammaOneAtlas318.quotient_localHomeomorph M hM
  obtain ⟨z,hz⟩ := GammaOneAtlas318.quotient_surjective M u
  obtain ⟨e,heZ,he⟩ := hqLoc z
  let B : Set UpperHalfPlane := e.source ∩ q ⁻¹' U
  have hB : IsOpen B := e.open_source.inter (hU.preimage hqLoc.continuous)
  have hzq : q z ∈ U := by rw [hz]; exact hu
  have hzB : z ∈ B := ⟨heZ,hzq⟩
  have hBI : InjOn q B := by
    intro x hx y hy h
    apply e.injOn hx.1 hy.1
    exact (congrFun he x).symm.trans (h.trans (congrFun he y))
  let W := q '' B
  have hWo : IsOpen W := hqLoc.isOpenMap B hB
  have hq : Measurable q :=
    measurable_quotient_mk' (s := MulAction.orbitRel (image M) UpperHalfPlane)
  have hWm : MeasurableSet W :=
    measurableSet_quotient.mpr (hWo.preimage hqLoc.continuous).measurableSet
  have hWU : W ⊆ U := by
    rintro v ⟨x,hx,rfl⟩
    exact hx.2
  have hPre : q ⁻¹' W ∩ B = B :=
    Set.inter_eq_right.mpr (fun x hx => ⟨x,hx,rfl⟩)
  have hEq : (area M hM).restrict W = ((volume : Measure UpperHalfPlane).restrict B).map q :=
    exact_period_sheet_area M hM B hB hBI
  have hm : area M hM W = (volume : Measure UpperHalfPlane) B := by
    have h := congrArg (fun ν : Measure (Base (image M)) => ν W) hEq
    simpa only [Measure.restrict_apply hWm, Measure.map_apply hq hWm,
      Measure.restrict_apply (hq hWm), Set.inter_self, hPre] using h
  have h0 : 0 < area M hM W := by
    rw [hm]
    exact upper_half_plane_open_pos B hB ⟨z,hzB⟩
  exact (h0.trans_le (measure_mono hWU)).ne'

end SelectedActualGammaOneAreaFullSupport318

#print axioms SelectedActualGammaOneAreaFullSupport318.actual_area_open_positive
