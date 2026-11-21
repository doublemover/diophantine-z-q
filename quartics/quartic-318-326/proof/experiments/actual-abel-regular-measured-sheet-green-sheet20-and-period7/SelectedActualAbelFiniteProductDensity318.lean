module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Algebra.BigOperators.Fin

public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal BigOperators

namespace SelectedActualAbelFiniteProductDensity318

variable {A : Type*} [MeasurableSpace A]

/-- Tonelli on the literal ordered finite family, including dimension zero. -/
theorem lintegral_coordinate_prod (n : ℕ) :
    ∀ (μ : Fin n → Measure A) [∀ i, SigmaFinite (μ i)]
      (f : Fin n → A → ℝ≥0∞) (_ : ∀ i, Measurable (f i)),
      (∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ)) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero =>
    intro μ _ f hf
    have he : (fun x : Fin 0 → A => ∏ i, f i (x i)) = fun _ => 1 := by
      funext x
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
    rw [he, lintegral_const, one_mul, Measure.pi_empty_univ]
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
  | succ n ih =>
    intro μ _ f hf
    let i : Fin (n+1) := 0
    let R : Fin n → Measure A := fun j => μ (i.succAbove j)
    let g : Fin n → A → ℝ≥0∞ := fun j => f (i.succAbove j)
    let e : (Fin (n+1) → A) ≃ᵐ (A × (Fin n → A)) :=
      MeasurableEquiv.piFinSuccAbove (fun _ => A) i
    have he : MeasurePreserving e (Measure.pi μ) ((μ i).prod (Measure.pi R)) :=
      measurePreserving_piFinSuccAbove μ i
    have hg (j : Fin n) : Measurable (g j) := hf (i.succAbove j)
    have hgprod : Measurable (fun x : Fin n → A => ∏ j, g j (x j)) :=
      Finset.measurable_fun_prod _ (fun j _ => (hg j).comp (measurable_pi_apply j))
    let F : A × (Fin n → A) → ℝ≥0∞ := fun x => f i x.1 * ∏ j, g j (x.2 j)
    calc
      (∫⁻ x, ∏ k, f k (x k) ∂(Measure.pi μ)) = ∫⁻ x, F (e x) ∂(Measure.pi μ) := by
        apply lintegral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        change (∏ k, f k (x k)) = f i (x i) * ∏ j : Fin n, f (i.succAbove j) (x (i.succAbove j))
        exact Fin.prod_univ_succAbove _ i
      _ = ∫⁻ x, F x ∂((μ i).prod (Measure.pi R)) :=
        he.lintegral_comp_emb e.measurableEmbedding F
      _ = (∫⁻ x, f i x ∂(μ i)) * ∫⁻ x, ∏ j, g j (x j) ∂(Measure.pi R) :=
        lintegral_prod_mul (hf i).aemeasurable hgprod.aemeasurable
      _ = (∫⁻ x, f i x ∂(μ i)) * ∏ j, ∫⁻ x, g j x ∂(R j) := by
        rw [ih R g hg]
      _ = ∏ k, ∫⁻ x, f k x ∂(μ k) :=
        (Fin.prod_univ_succAbove (fun k => ∫⁻ x, f k x ∂(μ k)) i).symm

/-- Density of a product of the actual scalar weighted measures. Applied to
UpperHalfPlane.volume_def, this gives the literal product hyperbolic density. -/
theorem pi_withDensity_coordinate_prod (n : ℕ) (μ : Fin n → Measure A)
    [∀ i, SigmaFinite (μ i)] (f : Fin n → A → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  apply Measure.pi_eq
  intro S hS
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS), Measure.restrict_pi_pi]
  calc
    (∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi (fun i => (μ i).restrict (S i)))) =
        ∏ i, ∫⁻ x, f i x ∂((μ i).restrict (S i)) :=
      lintegral_coordinate_prod n (fun i => (μ i).restrict (S i)) f hf
    _ = ∏ i, ((μ i).withDensity (f i)) (S i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact (withDensity_apply (f i) (hS i)).symm

end SelectedActualAbelFiniteProductDensity318

#print axioms SelectedActualAbelFiniteProductDensity318.pi_withDensity_coordinate_prod
