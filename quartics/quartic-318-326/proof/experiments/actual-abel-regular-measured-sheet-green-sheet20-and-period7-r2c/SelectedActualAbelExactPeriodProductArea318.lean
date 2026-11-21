module

public import SelectedActualAbelExactPeriodSheetArea318
public import SelectedGammaOneFinitePetersson318
public import Mathlib.MeasureTheory.Constructions.Pi

public section

noncomputable section

open UpperHalfPlane Set MeasureTheory MeasureTheory.Measure
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedGammaOneQuotientArea318 SelectedGammaOneFinitePetersson318
open SelectedActualAbelExactPeriodSheetArea318

namespace SelectedActualAbelExactPeriodProductArea318

/-- The exact product of the hyperbolic measures on actual injective period
sheets, pushed by the coordinatewise projection, is the restriction of the
same ordered quotient product area. No independent product or normalization
is used, and no point of the product is assumed Abel-regular. -/
theorem exact_ordered_period_product_area {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 5 ≤ N) (B : ι → Set UpperHalfPlane)
    (hB : ∀ i, IsOpen (B i)) (hBI : ∀ i, InjOn (quotientMap N) (B i)) :
    (Measure.pi (fun _ : ι => area N hN)).restrict
      (Set.univ.pi fun i => quotientMap N '' B i) =
    ((Measure.pi (fun _ : ι => (volume : Measure UpperHalfPlane))).restrict
      (Set.univ.pi B)).map (fun x i => quotientMap N (x i)) := by
  let q : UpperHalfPlane → Base (image N) := quotientMap N
  let R : ι → Measure UpperHalfPlane := fun i => volume.restrict (B i)
  let W : ι → Measure (Base (image N)) := fun i => (area N hN).restrict (q '' B i)
  have hq : Measurable q :=
    measurable_quotient_mk' (s := MulAction.orbitRel (image N) UpperHalfPlane)
  letI : IsFiniteMeasure (area N hN) := area_finite N hN
  have he (i : ι) : W i = (R i).map q := exact_period_sheet_area N hN (B i) (hB i) (hBI i)
  letI (i : ι) : SigmaFinite ((R i).map q) := by
    rw [← he i]
    change SigmaFinite ((area N hN).restrict (q '' B i))
    infer_instance
  have hprod : (Measure.pi R).map (fun x i => q (x i)) =
      Measure.pi (fun i => (R i).map q) :=
    Measure.pi_map_pi (μ := R) (f := fun _ => q) (fun _ => hq.aemeasurable)
  calc
    (Measure.pi (fun _ : ι => area N hN)).restrict (Set.univ.pi fun i => q '' B i) =
        Measure.pi W := Measure.restrict_pi_pi (fun _ : ι => area N hN) _
    _ = Measure.pi (fun i => (R i).map q) :=
      congrArg Measure.pi (funext he)
    _ = (Measure.pi R).map (fun x i => q (x i)) := hprod.symm
    _ = ((Measure.pi (fun _ : ι => (volume : Measure UpperHalfPlane))).restrict
          (Set.univ.pi B)).map (fun x i => q (x i)) :=
      congrArg (fun m : Measure (ι → UpperHalfPlane) => m.map (fun x i => q (x i)))
        (Measure.restrict_pi_pi (fun _ : ι => (volume : Measure UpperHalfPlane)) B).symm

end SelectedActualAbelExactPeriodProductArea318

#print axioms SelectedActualAbelExactPeriodProductArea318.exact_ordered_period_product_area
