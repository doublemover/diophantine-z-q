module

public import SelectedActualAbelWeightedPeriodProductMeasure318
public import SelectedActualAbelFlatPeriodProductCoordinates318
public import SelectedActualAbelActualTargetCoordinateSheet318

public section

noncomputable section

open Filter Matrix MeasureTheory MeasureTheory.Measure Set UpperHalfPlane
open scoped BigOperators ENNReal Topology
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedOriginalAbelMeasuredCover318 SelectedActualAbelOrdinaryChartDensity318
open SelectedActualAbelPointwiseDerivative318 SelectedActualAbelTargetLatticeHaar318
open SelectedActualAbelActualTargetCoordinateSheet318
open SelectedActualAbelFlatPeriodProductCoordinates318

namespace SelectedActualAbelGenuineLocalMeasuredSheet318

abbrev upstairs (g : ℕ) := Fin g → UpperHalfPlane

/-- The literal coordinatewise projection from the upstairs period product. -/
def periodProjection (M g : ℕ) (τ : upstairs g) : Domain M g :=
  fun i => quotientMap M (τ i)

abbrev upstairsRectangle {g : ℕ} (B : Fin g → Set UpperHalfPlane) : Set (upstairs g) :=
  Set.univ.pi B

abbrev flatRectangle {g : ℕ} (B : Fin g → Set UpperHalfPlane) :
    Set (OrderedPeriodCoordinates g) :=
  Set.univ.pi fun i => UpperHalfPlane.coe '' B i

/-- An actual sheet below, obtained by taking one coordinate sheet inside the
actual upstairs period rectangle. This need not be a product set. -/
def ordinarySheet (M g : ℕ) (B : Fin g → Set UpperHalfPlane)
    (S : Set (OrderedPeriodCoordinates g)) : Set (Domain M g) :=
  periodProjection M g '' (periodCoords ⁻¹' S ∩ upstairsRectangle B)

private theorem periodProjection_measurable (M g : ℕ) : Measurable (periodProjection M g) := by
  have hq : Measurable (quotientMap M) :=
    measurable_quotient_mk' (s := MulAction.orbitRel (image M) UpperHalfPlane)
  exact measurable_pi_iff.mpr (fun i => hq.comp (measurable_pi_apply i))

private theorem periodProjection_injOn {M g : ℕ} (B : Fin g → Set UpperHalfPlane)
    (hBi : ∀ i, InjOn (quotientMap M) (B i)) :
    InjOn (periodProjection M g) (upstairsRectangle B) := by
  intro τ hτ τ' hτ' he
  funext i
  exact hBi i (hτ i (Set.mem_univ i)) (hτ' i (Set.mem_univ i)) (congrFun he i)

/-- The genuine local pushforward in the actual quotient and same-J target.

The only geometric inputs are actual charts, degree-one holomorphic lifts
and their coefficients, the identity of the coordinate and ordinary maps,
and the fact that this is an injective sheet. The two local measures and
the ordered derivative are constructed by the preceding exact comparisons. -/
theorem actual_ordinary_abel_sheet {M g : ℕ} (hM : 5 ≤ M)
    (f : Fin g → SelectedWeightTwoPetersson318.Form M)
    {J ι : Type*} [AddCommGroup J] [MeasurableSpace J] [Finite ι]
    (L : Submodule ℤ (OrderedPeriodCoordinates g))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L)
    (q : OrderedPeriodCoordinates g →+ J) (hq : Measurable q)
    (hker : ∀ v : OrderedPeriodCoordinates g, q v = 0 ↔ v ∈ L)
    (a : Domain M g → J) (ha : Measurable a)
    (F : OrderedPeriodCoordinates g → OrderedPeriodCoordinates g) (hF : Measurable F)
    (C : OrderedPeriodCoordinates g → Matrix (Fin g) (Fin g) ℂ)
    (hC : Measurable (fun x => ENNReal.ofReal (Complex.normSq (C x).det)))
    (B : Fin g → Set UpperHalfPlane) (hB : ∀ i, IsOpen (B i))
    (hBi : ∀ i, InjOn (quotientMap M) (B i))
    (S U : Set (OrderedPeriodCoordinates g)) (hS : MeasurableSet S) (hSB : S ⊆ flatRectangle B)
    (hDown : MeasurableSet (ordinarySheet M g B S))
    (hU : MeasurableSet U) (hqi : InjOn q U) (hImageMeas : MeasurableSet (q '' U))
    (hCread : ∀ τ ∈ upstairsRectangle B, C (periodCoords τ) = periodMatrix f τ)
    (hRead : ∀ τ ∈ periodCoords ⁻¹' S ∩ upstairsRectangle B,
      a (periodProjection M g τ) = q (F (periodCoords τ)))
    (hgerm : ∀ x ∈ S, ∃ (φ : Fin g → Fin g → ℂ → ℂ) (c : OrderedPeriodCoordinates g),
      (∀ i j, HasDerivAt (φ i j) (C x i j) (x j)) ∧
      F =ᶠ[𝓝 x] fun z i => c i + ∑ j, φ i j (z j))
    (hFi : InjOn F S) (hFU : F '' S = U) :
    Measure.map a ((pullbackVolume f hM).restrict (ordinarySheet M g B S)) =
      (targetVolume L b (volume : Measure (OrderedPeriodCoordinates g)) q).restrict (q '' U) := by
  classical
  let p : upstairs g → Domain M g := periodProjection M g
  let R : Set (upstairs g) := upstairsRectangle B
  let T : Set (upstairs g) := periodCoords ⁻¹' S ∩ R
  let D : Set (Domain M g) := ordinarySheet M g B S
  let W : Set (Domain M g) := Set.univ.pi fun i => quotientMap M '' B i
  let μ : Measure (upstairs g) := Measure.pi (fun _ : Fin g => flatH)
  let w : OrderedPeriodCoordinates g → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Complex.normSq (C x).det)
  let flatWeighted : Measure (upstairs g) := μ.withDensity (fun τ => w (periodCoords τ))
  let coordWeighted : Measure (OrderedPeriodCoordinates g) := volume.withDensity w
  let m : Measure (upstairs g) := flatWeighted.restrict T
  have hp : Measurable p := periodProjection_measurable M g
  have hR : MeasurableSet R := MeasurableSet.univ_pi (fun i => (hB i).measurableSet)
  have hT : MeasurableSet T := (periodCoords_measurable hS).inter hR
  have hDW : D ⊆ W := by
    rintro x ⟨τ,hτ,rfl⟩
    intro i hi
    exact ⟨τ i,hτ.2 i hi,rfl⟩
  have hpre : p ⁻¹' D ∩ R = T := by
    ext τ
    constructor
    · intro hτ
      obtain ⟨σ,hσ,he⟩ := hτ.1
      exact (periodProjection_injOn B hBi hσ.2 hτ.2 he) ▸ hσ
    · intro hτ
      exact ⟨⟨τ,hτ,rfl⟩,hτ.2⟩
  have hW : (pullbackVolume f hM).restrict W = (flatWeighted.restrict R).map p := by
    have h := SelectedActualAbelWeightedPeriodProductMeasure318.actual_weighted_period_product_measure
      hM f B hB hBi
    have he :
        ((μ.withDensity fun τ => ENNReal.ofReal (Complex.normSq (periodMatrix f τ).det)).restrict R) =
          flatWeighted.restrict R := by
      change ((μ.withDensity fun τ => ENNReal.ofReal (Complex.normSq (periodMatrix f τ).det)).restrict R) =
        (μ.withDensity fun τ => w (periodCoords τ)).restrict R
      rw [restrict_withDensity hR, restrict_withDensity hR]
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem hR] with τ hτ
      change ENNReal.ofReal (Complex.normSq (periodMatrix f τ).det) =
        ENNReal.ofReal (Complex.normSq (C (periodCoords τ)).det)
      rw [hCread τ hτ]
    exact h.trans (congrArg (Measure.map p) he)
  have hD : (pullbackVolume f hM).restrict D = m.map p := by
    calc
      (pullbackVolume f hM).restrict D = ((pullbackVolume f hM).restrict W).restrict D :=
        (Measure.restrict_restrict_of_subset hDW).symm
      _ = ((flatWeighted.restrict R).map p).restrict D := congrArg (fun m => m.restrict D) hW
      _ = m.map p := by
        rw [Measure.restrict_map hp hDown, Measure.restrict_restrict (hp hDown), hpre]
  have hCoords : m.map periodCoords = coordWeighted.restrict S := by
    have h := flatProduct_weighted_chart B (fun i => (hB i).measurableSet) w hC
    rw [← MeasureTheory.volume_pi] at h
    calc
      m.map periodCoords = ((flatWeighted.restrict R).map periodCoords).restrict S := by
        rw [Measure.restrict_map periodCoords_measurable hS,
          Measure.restrict_restrict (periodCoords_measurable hS)]
      _ = (coordWeighted.restrict (flatRectangle B)).restrict S := congrArg (fun m => m.restrict S) h
      _ = coordWeighted.restrict S := Measure.restrict_restrict_of_subset hSB
  have hlocal := degreeOne_sheet_to_same_target L b
    (volume : Measure (OrderedPeriodCoordinates g)) q hq hker F hF C S U hS
    hU hqi hImageMeas hgerm hFi hFU
  calc
    Measure.map a ((pullbackVolume f hM).restrict D) = m.map (fun τ => a (p τ)) := by
      rw [hD, Measure.map_map ha hp] <;> rfl
    _ = m.map (fun τ => q (F (periodCoords τ))) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hT] with τ hτ
      exact hRead τ hτ
    _ = (m.map periodCoords).map (fun x => q (F x)) :=
      (Measure.map_map (hq.comp hF) periodCoords_measurable).symm
    _ = (coordWeighted.restrict S).map (fun x => q (F x)) :=
      congrArg (Measure.map (fun x => q (F x))) hCoords
    _ = (targetVolume L b (volume : Measure (OrderedPeriodCoordinates g)) q).restrict (q '' U) := by
      simpa only [coordWeighted, w, Complex.normSq_eq_norm_sq] using hlocal

end SelectedActualAbelGenuineLocalMeasuredSheet318

#print axioms SelectedActualAbelGenuineLocalMeasuredSheet318.actual_ordinary_abel_sheet
