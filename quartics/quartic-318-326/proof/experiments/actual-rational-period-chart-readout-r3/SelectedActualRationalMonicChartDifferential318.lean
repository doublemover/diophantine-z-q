module

public import SelectedActualRationalDifferentialPeriodDerivation318
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.AdjoinRoot

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

public section

noncomputable section

open Polynomial

namespace SelectedActualRationalMonicChartDifferential318

open SelectedActualRationalDifferentialPeriodDerivation318

/-- This is the literal rational ordinary denominator in the fixed compact
chart, not a further localization invented for the comparison. -/
@[expose] def actualOrdinaryDenominator : ℚ[X] := X * (X - C 1728)

abbrev R := Localization.Away actualOrdinaryDenominator
abbrev A (p : R[X]) := AdjoinRoot p

@[expose] def baseIntoRoot (p : R[X]) : ℚ[X] →+* A p :=
  (algebraMap R (A p)).comp (algebraMap ℚ[X] R)

@[expose] def parameter (p : R[X]) : A p := baseIntoRoot p Polynomial.X

private theorem baseIntoRoot_C (p : R[X]) (c : ℚ) :
    baseIntoRoot p (Polynomial.C c) = algebraMap ℚ (A p) c := by
  have hr : algebraMap ℚ R c = algebraMap ℚ[X] R (Polynomial.C c) :=
    IsScalarTower.algebraMap_apply ℚ ℚ[X] R c
  have ha : algebraMap ℚ (A p) c = algebraMap R (A p) (algebraMap ℚ R c) :=
    IsScalarTower.algebraMap_apply ℚ R (A p) c
  exact (ha.trans (congrArg (algebraMap R (A p)) hr)).symm

private theorem differentiable_polynomial_coeff (p : R[X]) (e : ℂ → A p →ₐ[ℚ] ℂ) (τ : ℂ)
    (hJ : DifferentiableAt ℂ (fun z => e z (parameter p)) τ) (f : ℚ[X]) :
    DifferentiableAt ℂ (fun z => e z (baseIntoRoot p f)) τ := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    have hfun : (fun z : ℂ => e z (baseIntoRoot p (f + g))) =
        (fun z : ℂ => e z (baseIntoRoot p f) + e z (baseIntoRoot p g)) := by
      funext z
      simp only [map_add]
    rw [hfun]
    exact DifferentiableAt.fun_add hf hg
  | monomial n c =>
    have hc : DifferentiableAt ℂ (fun _ : ℂ => algebraMap ℚ ℂ c) τ :=
      differentiableAt_const _
    have hh : DifferentiableAt ℂ (fun z => algebraMap ℚ ℂ c * (e z (parameter p))^n) τ := by
      exact DifferentiableAt.fun_mul hc (hJ.hasDerivAt.fun_pow n).differentiableAt
    simpa only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, baseIntoRoot_C,
      AlgHom.commutes, parameter] using hh

private theorem differentiable_localized_coeff (p : R[X]) (e : ℂ → A p →ₐ[ℚ] ℂ) (τ : ℂ)
    (hJ : DifferentiableAt ℂ (fun z => e z (parameter p)) τ) (r : R) :
    DifferentiableAt ℂ (fun z => e z (algebraMap R (A p) r)) τ := by
  let k : ℚ[X] × ℕ := IsLocalization.Away.sec actualOrdinaryDenominator r
  have hsec : r * algebraMap ℚ[X] R (actualOrdinaryDenominator ^ k.2) =
      algebraMap ℚ[X] R k.1 := IsLocalization.Away.sec_spec actualOrdinaryDenominator r
  have huR : IsUnit (algebraMap ℚ[X] R actualOrdinaryDenominator) :=
    IsLocalization.Away.algebraMap_isUnit (S := R) actualOrdinaryDenominator
  have hu (z : ℂ) : e z (baseIntoRoot p actualOrdinaryDenominator) ≠ 0 :=
    ((huR.map (algebraMap R (A p))).map (e z).toRingHom).ne_zero
  have hfun : (fun z => e z (algebraMap R (A p) r)) =
      (fun z => e z (baseIntoRoot p k.1) /
        (e z (baseIntoRoot p actualOrdinaryDenominator)) ^ k.2) := by
    funext z
    have he := congrArg (fun r : R => e z (algebraMap R (A p) r)) hsec
    apply (eq_div_iff (pow_ne_zero _ (hu z))).mpr
    simpa only [map_mul, map_pow, baseIntoRoot, RingHom.comp_apply] using he
  rw [hfun]
  have hf := differentiable_polynomial_coeff p e τ hJ k.1
  have hd :
      DifferentiableAt ℂ (fun z => (e z (baseIntoRoot p actualOrdinaryDenominator)) ^ k.2) τ :=
    ((differentiable_polynomial_coeff p e τ hJ actualOrdinaryDenominator).hasDerivAt.fun_pow
      k.2).differentiableAt
  exact DifferentiableAt.fun_div hf hd (pow_ne_zero _ (hu τ))

/-- For the literal rational monic ordinary algebra, differentiability of
the two actual period coordinates suffices for every actual ring element.
This includes denominators, rather than silently treating the open as
an unlocalized polynomial chart. -/
theorem differentiable_actual_monic_chart (p : R[X]) (e : ℂ → A p →ₐ[ℚ] ℂ) (τ : ℂ)
    (hJ : DifferentiableAt ℂ (fun z => e z (parameter p)) τ)
    (hX : DifferentiableAt ℂ (fun z => e z (AdjoinRoot.root p)) τ)
    (r : A p) : DifferentiableAt ℂ (fun z => e z r) τ := by
  refine AdjoinRoot.induction_on p r fun f => ?_
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    have hfun : (fun z : ℂ => e z (AdjoinRoot.mk p (f + g))) =
        (fun z : ℂ => e z (AdjoinRoot.mk p f) + e z (AdjoinRoot.mk p g)) := by
      funext z
      simp only [map_add]
    rw [hfun]
    exact DifferentiableAt.fun_add hf hg
  | monomial n c =>
    have hc := differentiable_localized_coeff p e τ hJ c
    have hh :
        DifferentiableAt ℂ (fun z =>
          e z (algebraMap R (A p) c) * (e z (AdjoinRoot.root p)) ^ n) τ := by
      exact DifferentiableAt.fun_mul hc (hX.hasDerivAt.fun_pow n).differentiableAt
    simpa only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
      AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq] using hh

/-- Actual dJ-normalized coefficient on the rational ordinary monic chart,
assuming the original period family agrees on the literal pair of
coordinate evaluations. No derivative condition is assumed for other
regular functions and there is no division by j prime. -/
theorem actual_monic_chart_period_differential (p : R[X]) (e : ℂ → A p →ₐ[ℚ] ℂ) (τ : ℂ)
    (hJ : DifferentiableAt ℂ (fun z => e z (parameter p)) τ)
    (hX : DifferentiableAt ℂ (fun z => e z (AdjoinRoot.root p)) τ)
    (frame : KaehlerDifferential ℚ (A p) ≃ₗ[A p] (A p))
    (hframe : frame (KaehlerDifferential.D ℚ (A p) (parameter p)) = 1)
    (ω : KaehlerDifferential ℚ (A p)) :
    letI : Algebra (A p) ℂ := (e τ).toRingHom.toAlgebra
    letI : IsScalarTower ℚ (A p) ℂ :=
      IsScalarTower.of_algebraMap_eq (fun c => ((e τ).commutes c).symm)
    Derivation.liftKaehlerDifferential
      (evaluationDerivation e τ (differentiable_actual_monic_chart p e τ hJ hX)) ω = e τ (frame ω) * deriv (fun z => e z (parameter p)) τ :=
  pullback_normalized_differential e τ (differentiable_actual_monic_chart p e τ hJ hX)
    (parameter p) frame hframe ω

end SelectedActualRationalMonicChartDifferential318

#print axioms SelectedActualRationalMonicChartDifferential318.actual_monic_chart_period_differential
