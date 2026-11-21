module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

public section

noncomputable section

open Set MeasureTheory MeasureTheory.Measure UpperHalfPlane
open scoped ENNReal

namespace SelectedActualAbelFlatPeriodProductCoordinates318

abbrev flatH : Measure UpperHalfPlane := (volume : Measure ℂ).comap UpperHalfPlane.coe

def periodCoords {ι : Type*} (x : ι → UpperHalfPlane) : ι → ℂ :=
  fun i => (x i : ℂ)

theorem periodCoords_measurable {ι : Type*} : Measurable (periodCoords (ι := ι)) :=
  measurable_pi_iff.mpr (fun i => measurable_coe.comp (measurable_pi_apply i))

theorem periodCoords_injective {ι : Type*} : Function.Injective (periodCoords (ι := ι)) := by
  intro x y h
  funext i
  exact measurableEmbedding_coe.injective (congrFun h i)

theorem sourceRect_preimage_targetRect {ι : Type*}
    (B : ι → Set UpperHalfPlane) :
    periodCoords ⁻¹' (Set.univ.pi (fun i => UpperHalfPlane.coe '' B i)) =
      Set.univ.pi B := by
  ext x
  constructor
  · intro hx i hi
    obtain ⟨y,hy,hye⟩ := hx i hi
    have h : y = x i := measurableEmbedding_coe.injective hye
    exact h ▸ hy
  · intro hx i hi
    exact ⟨x i,hx i hi,rfl⟩

/-- The actual complex coordinates on an ordered product period rectangle
carry the actual Euclidean reference measure to standard complex product
Lebesgue measure restricted to that precise rectangular image. -/
theorem flatProduct_map_restrict {ι : Type*} [Fintype ι]
    (B : ι → Set UpperHalfPlane) (hB : ∀ i, MeasurableSet (B i)) :
    ((Measure.pi (fun _ : ι => flatH)).restrict (Set.univ.pi B)).map periodCoords =
      (Measure.pi (fun _ : ι => (volume : Measure ℂ))).restrict
        (Set.univ.pi (fun i => UpperHalfPlane.coe '' B i)) := by
  let W : Set (ι → ℂ) := Set.univ.pi (fun i => UpperHalfPlane.coe '' B i)
  let R : Set (ι → ℂ) := Set.univ.pi (fun _ => Set.range UpperHalfPlane.coe)
  have hW : MeasurableSet W :=
    MeasurableSet.univ_pi (fun i => measurableEmbedding_coe.measurableSet_image.mpr (hB i))
  have hWR : W ⊆ R := fun x hx i hi => Set.image_subset_range _ _ (hx i hi)
  have h₁ : flatH.map UpperHalfPlane.coe = (volume : Measure ℂ).restrict
      (Set.range UpperHalfPlane.coe) := measurableEmbedding_coe.map_comap
  letI : SigmaFinite (flatH.map UpperHalfPlane.coe) := by
    rw [h₁]
    infer_instance
  have hfull :
      (Measure.pi (fun _ : ι => flatH)).map periodCoords =
        (Measure.pi (fun _ : ι => (volume : Measure ℂ))).restrict R := by
    calc
      (Measure.pi (fun _ : ι => flatH)).map periodCoords =
          Measure.pi (fun _ : ι => flatH.map UpperHalfPlane.coe) :=
        Measure.pi_map_pi (μ := fun _ => flatH) (f := fun _ => UpperHalfPlane.coe)
          (fun _ => measurable_coe.aemeasurable)
      _ = (Measure.pi (fun _ : ι => (volume : Measure ℂ))).restrict R := by
        rw [Measure.restrict_pi_pi]
        exact congrArg Measure.pi (funext fun _ => h₁)
  change ((Measure.pi (fun _ : ι => flatH)).restrict (Set.univ.pi B)).map periodCoords =
    (Measure.pi (fun _ : ι => (volume : Measure ℂ))).restrict W
  rw [← sourceRect_preimage_targetRect B, ← Measure.restrict_map periodCoords_measurable hW,
    hfull, Measure.restrict_restrict hW, Set.inter_eq_left.mpr hWR]

private theorem withDensity_map_explicit {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (q : X → Y) (hq : Measurable q) (μ : Measure X) (w : Y → ℝ≥0∞)
    (hw : Measurable w) :
    (μ.withDensity (fun x => w (q x))).map q = (μ.map q).withDensity w := by
  ext1 U hU
  rw [withDensity_apply w hU, Measure.restrict_map hq hU, lintegral_map hw hq,
    Measure.map_apply hq hU, withDensity_apply _ (hq hU)]

/-- Determinant weight is transported in the original Euclidean coordinates
with the same reference complex Lebesgue measure as the local Jacobian. -/
theorem flatProduct_weighted_chart {ι : Type*} [Fintype ι]
    (B : ι → Set UpperHalfPlane) (hB : ∀ i, MeasurableSet (B i))
    (w : (ι → ℂ) → ℝ≥0∞) (hw : Measurable w) :
    (((Measure.pi (fun _ : ι => flatH)).withDensity (fun x => w (periodCoords x))).restrict
      (Set.univ.pi B)).map periodCoords =
      ((Measure.pi (fun _ : ι => (volume : Measure ℂ))).withDensity w).restrict
        (Set.univ.pi (fun i => UpperHalfPlane.coe '' B i)) := by
  have hS : MeasurableSet (Set.univ.pi B) := MeasurableSet.univ_pi hB
  have hT : MeasurableSet (Set.univ.pi (fun i => UpperHalfPlane.coe '' B i)) :=
    MeasurableSet.univ_pi (fun i => measurableEmbedding_coe.measurableSet_image.mpr (hB i))
  rw [restrict_withDensity hS, withDensity_map_explicit periodCoords periodCoords_measurable _ w hw,
    flatProduct_map_restrict B hB, ← restrict_withDensity hT]

end SelectedActualAbelFlatPeriodProductCoordinates318

#print axioms SelectedActualAbelFlatPeriodProductCoordinates318.flatProduct_weighted_chart
