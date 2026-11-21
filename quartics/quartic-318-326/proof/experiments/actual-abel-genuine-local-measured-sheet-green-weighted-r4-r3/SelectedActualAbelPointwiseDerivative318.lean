module

public import SelectedActualAbelComplexSheetJacobian318
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.LinearAlgebra.Determinant

public section

noncomputable section

open Filter Matrix MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace SelectedActualAbelPointwiseDerivative318

open SelectedActualAbelComplexSheetJacobian318

abbrev OrderedPeriodCoordinates (g : ℕ) := Fin g → ℂ

private abbrev columnTerm {g : ℕ} (c : ℂ) (j : Fin g) :
    OrderedPeriodCoordinates g →L[ℂ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ c).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) j)

/-- The continuous linear map with column j equal to the actual evaluations
of the ordered invariant differentials on source tangent j. -/
def abelLinear {g : ℕ} (C : Matrix (Fin g) (Fin g) ℂ) :
    OrderedPeriodCoordinates g →L[ℂ] OrderedPeriodCoordinates g :=
  ContinuousLinearMap.pi (fun i => ∑ j, columnTerm (C i j) j)

theorem abelLinear_entry {g : ℕ} (C : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g) :
    abelLinear C (Pi.single j 1) i = C i j := by
  classical
  unfold abelLinear
  rw [ContinuousLinearMap.pi_apply, _root_.sum_apply]
  rw [Finset.sum_eq_single j]
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      Pi.single_eq_same, ContinuousLinearMap.toSpanSingleton_apply_one]
  · intro k _ hk
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      Pi.single_eq_of_ne hk, ContinuousLinearMap.toSpanSingleton_apply, zero_smul]
  · intro hj
    exact False.elim (hj (Finset.mem_univ _))

theorem abelLinear_matrix {g : ℕ} (C : Matrix (Fin g) (Fin g) ℂ) :
    LinearMap.toMatrix' (abelLinear C).toLinearMap = C := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  exact abelLinear_entry C i j

theorem abelLinear_det {g : ℕ} (C : Matrix (Fin g) (Fin g) ℂ) :
    (abelLinear C).toLinearMap.det = C.det :=
  (LinearMap.det_toMatrix' _).symm.trans (congrArg Matrix.det (abelLinear_matrix C))

/-- Differentiate the literal sum of local lifts of the degree-one Abel map.
Only the derivatives of the one-variable invariant pullbacks and the actual
sum germ are assumed; a derivative of the ordered Abel map is not an input.
The constant covers the difference of any two local lifts by a lattice element. -/
theorem hasFDerivAt_abelSum_of_degreeOne {g : ℕ}
    (τ : OrderedPeriodCoordinates g) (a : Fin g → Fin g → ℂ → ℂ)
    (c : OrderedPeriodCoordinates g) (C : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ i j, HasDerivAt (a i j) (C i j) (τ j))
    (F : OrderedPeriodCoordinates g → OrderedPeriodCoordinates g)
    (hF : F =ᶠ[𝓝 τ] fun x i => c i + ∑ j, a i j (x j)) :
    HasFDerivAt F (abelLinear C) τ := by
  classical
  have hs (i : Fin g) :
      HasFDerivAt (fun x : OrderedPeriodCoordinates g => ∑ j, a i j (x j))
        (∑ j, columnTerm (C i j) j) τ := by
    have hc (j : Fin g) :
        HasFDerivAt (fun x : OrderedPeriodCoordinates g => a i j (x j))
          (columnTerm (C i j) j) τ :=
      (h i j).hasFDerivAt.comp τ (hasFDerivAt_apply j τ)
    exact HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hc j)
  have hrow (i : Fin g) :
      HasFDerivAt (fun x : OrderedPeriodCoordinates g => c i + ∑ j, a i j (x j))
        (∑ j, columnTerm (C i j) j) τ := (hs i).const_add (c i)
  have ha : HasFDerivAt (fun x i => c i + ∑ j, a i j (x j)) (abelLinear C) τ := by
    unfold abelLinear
    exact hasFDerivAt_pi.mpr hrow
  exact ha.congr_of_eventuallyEq hF

/-- The same local lemma now constructs, rather than assumes, the sheet
pushforward with the determinant of the *actual* ordered degree-one rows. -/
theorem sheet_pushforward_of_degreeOne {g : ℕ}
    (μ : Measure (OrderedPeriodCoordinates g)) [Measure.IsAddHaarMeasure μ]
    (F : OrderedPeriodCoordinates g → OrderedPeriodCoordinates g)
    (C : OrderedPeriodCoordinates g → Matrix (Fin g) (Fin g) ℂ)
    (S U : Set (OrderedPeriodCoordinates g)) (hS : MeasurableSet S)
    (hgerm : ∀ τ ∈ S, ∃ (a : Fin g → Fin g → ℂ → ℂ) (c : OrderedPeriodCoordinates g),
      (∀ i j, HasDerivAt (a i j) (C τ i j) (τ j)) ∧
      F =ᶠ[𝓝 τ] fun x i => c i + ∑ j, a i j (x j))
    (hinj : InjOn F S) (himage : F '' S = U) :
    Measure.map F
      ((μ.withDensity fun τ => ENNReal.ofReal (‖(C τ).det‖ ^ 2)).restrict S)
      = μ.restrict U := by
  have hd (τ) (hτ : τ ∈ S) : HasFDerivWithinAt F (abelLinear (C τ)) S τ := by
    obtain ⟨a,c,ha,hF⟩ := hgerm τ hτ
    exact (hasFDerivAt_abelSum_of_degreeOne τ a c (C τ) ha F hF).hasFDerivWithinAt
  simpa only [abelLinear_det] using
    complex_density_sheet_pushforward μ F (fun τ => abelLinear (C τ))
      S U hS hd hinj himage

end SelectedActualAbelPointwiseDerivative318

#print axioms SelectedActualAbelPointwiseDerivative318.hasFDerivAt_abelSum_of_degreeOne
#print axioms SelectedActualAbelPointwiseDerivative318.abelLinear_det
#print axioms SelectedActualAbelPointwiseDerivative318.sheet_pushforward_of_degreeOne
