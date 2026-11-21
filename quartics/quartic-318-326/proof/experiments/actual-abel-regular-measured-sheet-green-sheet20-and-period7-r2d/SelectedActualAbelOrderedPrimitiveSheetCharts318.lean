module

public import SelectedActualAbelPeriodFromIdentityDifferential318
public import SelectedActualAbelPointwiseDerivative318
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import all SelectedActualOrdinaryAbelPeriodMap318
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic

public section

noncomputable section

open Filter Function Set UpperHalfPlane
open scoped BigOperators Topology
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedWeightTwoPetersson318 SelectedActualOrdinaryAbelPeriodMap318
open SelectedActualAbelPeriodAgreement318 SelectedActualAbelPeriodFromIdentityDifferential318
open SelectedActualAbelIdentityChartLifts318 SelectedActualAbelPointwiseDerivative318

namespace SelectedActualAbelOrderedPrimitiveSheetCharts318

variable {M g : ℕ}

abbrev V (g : ℕ) := OrderedPeriodCoordinates g

abbrev fullPeriods (g : ℕ) : Set (V g) := Set.univ.pi (fun _ => upperHalfPlaneSet)

theorem fullPeriods_open (g : ℕ) : IsOpen (fullPeriods g) :=
  isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_upperHalfPlaneSet)

def rowMatrix (f : Fin g → Form M) (x : V g) : Matrix (Fin g) (Fin g) ℂ :=
  fun i j => f i (UpperHalfPlane.ofComplex (x j))

theorem rowMatrix_coe (f : Fin g → Form M) (t : Fin g → UpperHalfPlane) :
    rowMatrix f (fun j => (t j : ℂ)) = fun i j => f i (t j) := by
  funext i j
  change f i (UpperHalfPlane.ofComplex (t j : ℂ)) = f i (t j)
  rw [UpperHalfPlane.ofComplex_apply]

def translation (c : V g) : V g := ∑ _ : Fin g, c

def uncut (f : Fin g → Form M) (c : V g) (x : V g) : V g :=
  fun i => translation c i + ∑ j : Fin g, primitive (f i) (x j)

/-- The actual ordered primitive sum in the original frame. Outside the
open period product, use the zero extension only to give a globally
measurable coordinate function for the measure pushforward. -/
def liftSum (f : Fin g → Form M) (c : V g) : V g → V g := by
  classical
  exact (fullPeriods g).piecewise (uncut f c) (fun _ => 0)

theorem liftSum_apply (f : Fin g → Form M) (c x : V g) (hx : x ∈ fullPeriods g) :
    liftSum f c x = uncut f c x := by
  classical
  unfold liftSum
  exact Set.piecewise_eq_of_mem _ _ _ hx

theorem liftSum_germ (f : Fin g → Form M) (c x : V g) (hx : x ∈ fullPeriods g) :
    liftSum f c =ᶠ[𝓝 x]
      (fun y i => translation c i + ∑ j : Fin g, primitive (f i) (y j)) := by
  exact ((fullPeriods_open g).eventually_mem hx).mono
    (fun y hy => liftSum_apply f c y hy)

private theorem primitive_derivative (f : Form M) {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    HasDerivAt (primitive f) (f (UpperHalfPlane.ofComplex z)) z := by
  let t : UpperHalfPlane := ⟨z,hz⟩
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  exact primitive_hasDerivAt f t

theorem liftSum_column (f : Fin g → Form M) (x : V g) (hx : x ∈ fullPeriods g)
    (i j : Fin g) :
    HasDerivAt (primitive (f i)) (rowMatrix f x i j) (x j) := by
  unfold rowMatrix
  exact primitive_derivative (f i) (hx j (Set.mem_univ j))

/-- There is no supplied ordered germ or derivative: every coordinate is
the exact fixed one-variable primitive, in the original order. -/
theorem liftSum_hasFDerivAt (f : Fin g → Form M) (c x : V g)
    (hx : x ∈ fullPeriods g) :
    HasFDerivAt (liftSum f c) (abelLinear (rowMatrix f x)) x :=
  hasFDerivAt_abelSum_of_degreeOne x (fun i _ => primitive (f i)) (translation c)
    (rowMatrix f x) (liftSum_column f x hx) (liftSum f c) (liftSum_germ f c x hx)

private theorem primitive_analytic (f : Form M) {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    AnalyticAt ℂ (primitive f) z := by
  have h : DifferentiableOn ℂ (primitive f) upperHalfPlaneSet :=
    fun _ hy => (primitive_derivative f hy).differentiableAt.differentiableWithinAt
  exact h.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds hz)

private theorem uncut_analytic (f : Fin g → Form M) (c x : V g) (hx : x ∈ fullPeriods g) :
    AnalyticAt ℂ (uncut f c) x := by
  unfold uncut
  apply AnalyticAt.pi
  intro i
  have h : AnalyticAt ℂ (fun y : V g => ∑ j : Fin g, primitive (f i) (y j)) x := by
    apply Finset.analyticAt_fun_sum Finset.univ
    intro j _
    let pj : V g →L[ℂ] ℂ :=
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) j
    have hOuter : AnalyticAt ℂ (primitive (f i)) (pj x) :=
      primitive_analytic (f i) (by simpa only [pj, ContinuousLinearMap.proj_apply] using
        hx j (Set.mem_univ j))
    have hComp : AnalyticAt ℂ (primitive (f i) ∘ (pj : V g → ℂ)) x :=
      hOuter.compContinuousLinearMap (u := pj)
    simpa only [Function.comp_def, pj, ContinuousLinearMap.proj_apply] using hComp
  exact (analyticAt_const (v := translation c i)).fun_add h

theorem liftSum_hasStrictFDerivAt (f : Fin g → Form M) (c x : V g)
    (hx : x ∈ fullPeriods g) :
    HasStrictFDerivAt (liftSum f c) (abelLinear (rowMatrix f x)) x := by
  have hn : AnalyticAt ℂ (liftSum f c) x :=
    (uncut_analytic f c x hx).congr (liftSum_germ f c x hx).symm
  have hd := liftSum_hasFDerivAt f c x hx
  simpa only [hd.fderiv] using hn.hasStrictFDerivAt

theorem liftSum_measurable (f : Fin g → Form M) (c : V g) : Measurable (liftSum f c) := by
  classical
  unfold liftSum
  exact (show ContinuousOn (uncut f c) (fullPeriods g) from
    fun x hx => (uncut_analytic f c x hx).continuousAt.continuousWithinAt).measurable_piecewise
      continuousOn_const (fullPeriods_open g).measurableSet

variable {J : Type*} [AddCommGroup J]

theorem liftSum_same_original_map (f : Fin g → Form M) (q : V g →+ J)
    (a : Base (image M) → J) (hLocal : LocalOriginalLifts f q a)
    (c : V g) (hc : q c = a (quotientMap M UpperHalfPlane.I))
    (t : Fin g → UpperHalfPlane) :
    q (liftSum f c (fun j => (t j : ℂ))) = ∑ j : Fin g, a (quotientMap M (t j)) := by
  have ht : (fun j => (t j : ℂ)) ∈ fullPeriods g := fun j _ => (t j).im_pos
  have hsum : uncut f c (fun j => (t j : ℂ)) =
      ∑ j : Fin g, (primitiveVector f (t j) + c) := by
    funext i
    let pr : V g →L[ℂ] ℂ :=
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) i
    have hL : translation c i = ∑ _ : Fin g, c i := by
      change pr (∑ _ : Fin g, c) = _
      rw [map_sum] <;> simp only [pr, ContinuousLinearMap.proj_apply]
    have hR : (∑ j : Fin g, (primitiveVector f (t j) + c)) i =
        ∑ j : Fin g, (primitive (f i) (t j : ℂ) + c i) := by
      change pr (∑ j : Fin g, (primitiveVector f (t j) + c)) = _
      rw [map_sum] <;> simp only [pr, ContinuousLinearMap.proj_apply, Pi.add_apply, primitiveVector]
    change translation c i + (∑ j : Fin g, primitive (f i) (t j : ℂ)) =
      (∑ j : Fin g, (primitiveVector f (t j) + c)) i
    rw [hL, hR, Finset.sum_add_distrib]
    exact add_comm _ _
  rw [liftSum_apply f c _ ht,hsum,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_add,hc]
  exact (original_value_from_local_lifts f q a hLocal (t j)).symm

variable [TopologicalSpace J] [IsTopologicalAddGroup J]

/-- One translation of the exact primitive gives the entire ordered map
of degree-one Abel sums, not only independent local charts or unrelated
lifts. The geometric input is its actual invariant differential. -/
theorem exists_ordered_lift_from_invariant_differential (hM : 5 ≤ M)
    (f : Fin g → Form M) (q : V g →+ J) (hq : Continuous q) (hSurj : Surjective q)
    (chart : IdentityChart q) (a : Base (image M) → J) (ha : Continuous a)
    (hread : InvariantDifferentialEquation f chart a) :
    ∃ c : V g, Measurable (liftSum f c) ∧
      (∀ t : Fin g → UpperHalfPlane,
        q (liftSum f c (fun j => (t j : ℂ))) = ∑ j : Fin g, a (quotientMap M (t j))) ∧
      ∀ x ∈ fullPeriods g, HasStrictFDerivAt (liftSum f c) (abelLinear (rowMatrix f x)) x := by
  obtain ⟨c,hc⟩ := hSurj (a (quotientMap M UpperHalfPlane.I))
  refine ⟨c,liftSum_measurable f c,?_,fun x hx => liftSum_hasStrictFDerivAt f c x hx⟩
  exact liftSum_same_original_map f q a (actual_local_original_lifts hM f q hq hSurj chart a ha hread) c hc

/-- Invertibility of the literal period matrix constructs a true sheet
of this same coordinate function. It may be simultaneously restricted
to any specified source rectangle and any actual q-injective target
chart; neither injectivity of the sheet nor its image is supplied. -/
theorem exists_regular_ordered_sheet (f : Fin g → Form M) (c x : V g)
    (R W : Set (V g)) (hR : IsOpen R) (hW : IsOpen W)
    (hRx : x ∈ R) (hRall : R ⊆ fullPeriods g) (hWx : liftSum f c x ∈ W)
    (hdet : (rowMatrix f x).det ≠ 0) :
    ∃ S U : Set (V g), IsOpen S ∧ IsOpen U ∧ x ∈ S ∧ S ⊆ R ∧ U ⊆ W ∧
      InjOn (liftSum f c) S ∧ liftSum f c '' S = U ∧
      ∀ T : Set (V g), IsOpen T → T ⊆ S → IsOpen (liftSum f c '' T) := by
  let d : V g →L[ℂ] V g := abelLinear (rowMatrix f x)
  have hd : d.toLinearMap.det ≠ 0 := by
    intro hz
    exact hdet ((abelLinear_det (rowMatrix f x)).symm.trans hz)
  have hker : LinearMap.ker d.toLinearMap = ⊥ := by
    by_contra h
    exact hd (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hi : Injective d.toLinearMap := LinearMap.ker_eq_bot.mp hker
  have hs : Surjective d.toLinearMap := LinearMap.injective_iff_surjective.mp hi
  let D : V g ≃L[ℂ] V g := (LinearEquiv.ofBijective d.toLinearMap ⟨hi,hs⟩).toContinuousLinearEquiv
  have hD : (D : V g →L[ℂ] V g) = d := by
    ext y
    rfl
  have hF : HasStrictFDerivAt (liftSum f c) (D : V g →L[ℂ] V g) x := by
    rw [hD]
    exact liftSum_hasStrictFDerivAt f c x (hRall hRx)
  let e : OpenPartialHomeomorph (V g) (V g) := hF.toOpenPartialHomeomorph (liftSum f c)
  have he : (e : V g → V g) = liftSum f c := hF.toOpenPartialHomeomorph_coe
  have hxe : x ∈ e.source := hF.mem_toOpenPartialHomeomorph_source
  let S : Set (V g) := (e.source ∩ e ⁻¹' W) ∩ R
  have hS : IsOpen S := (e.isOpen_inter_preimage hW).inter hR
  have hSe : S ⊆ e.source := fun _ hy => hy.1.1
  have hSx : x ∈ S := by
    have h : e x ∈ W := by
      change (e : V g → V g) x ∈ W
      rw [he]
      exact hWx
    exact ⟨⟨hxe,h⟩,hRx⟩
  refine ⟨S,e '' S,hS,e.isOpen_image_of_subset_source hS hSe,hSx,inter_subset_right,?_,?_,?_,?_⟩
  · rintro _ ⟨y,hy,rfl⟩
    exact hy.1.2
  · rw [← he]
    exact e.injOn.mono hSe
  · exact congrArg (fun F : V g → V g => F '' S) he.symm
  · intro T hT hTS
    rw [← he]
    exact e.isOpen_image_of_subset_source hT (hTS.trans hSe)

end SelectedActualAbelOrderedPrimitiveSheetCharts318

#print axioms SelectedActualAbelOrderedPrimitiveSheetCharts318.exists_ordered_lift_from_invariant_differential
#print axioms SelectedActualAbelOrderedPrimitiveSheetCharts318.exists_regular_ordered_sheet
