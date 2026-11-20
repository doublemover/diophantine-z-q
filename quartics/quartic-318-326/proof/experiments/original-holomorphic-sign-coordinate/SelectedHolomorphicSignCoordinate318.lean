module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
public section
noncomputable section

namespace SelectedHolomorphicSignCoordinate318

/-- The normalized abscissa is free of any choice of sign for the
scaling square root. A,B are the source short coefficients and x its
actual marked abscissa. -/
@[expose] def abscissa (A B x : ℂ) : ℂ := (2*A/(3*B))*x

/-- When scaling to the literal ordinary short model (-3v,-2v),
every legitimate root yields the same normalized abscissa. -/
theorem same_scaled_abscissa (A B v x : ℂ) (s : ℂˣ) (hB : B ≠ 0)
    (scaledA : (s:ℂ)^4*A = -3*v) (scaledB : (s:ℂ)^6*B = -2*v) :
    (s:ℂ)^2*x = abscissa A B x := by
  have hden : 3*B ≠ 0 := mul_ne_zero (by norm_num) hB
  have h : (s:ℂ)^4 * ((s:ℂ)^2*(3*B)-2*A) = 0 := by
    linear_combination 3*scaledB-2*scaledA
  have hz : (s:ℂ)^2*(3*B)-2*A = 0 :=
    (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ s.ne_zero)
  have hs : (s:ℂ)^2 = 2*A/(3*B) := (eq_div_iff hden).mpr (sub_eq_zero.mp hz)
  rw [hs,abscissa]

/-- The genuine period functions, when supplied by uniformization,
yield a continuous map into the actual (J,x) ordinary sign
coordinates without needing a continuous choice of a square root. -/
theorem continuous_coordinates {T : Type*} [TopologicalSpace T] (U : Set T)
    (J A B markX : T → ℂ) (hJ : ContinuousOn J U)
    (hA : ContinuousOn A U) (hB : ContinuousOn B U) (hX : ContinuousOn markX U)
    (nonzeroB : ∀ z ∈ U, B z ≠ 0) :
    ContinuousOn (fun z => (J z, abscissa (A z) (B z) (markX z))) U := by
  have hTwo : ContinuousOn (fun z => (2:ℂ)*A z) U := continuousOn_const.mul hA
  have hThree : ContinuousOn (fun z => (3:ℂ)*B z) U := continuousOn_const.mul hB
  have hDen : ∀ z ∈ U, (3:ℂ)*B z ≠ 0 := fun z hz =>
    mul_ne_zero (by norm_num) (nonzeroB z hz)
  exact hJ.prodMk ((hTwo.div hThree hDen).mul hX)

end SelectedHolomorphicSignCoordinate318

#print axioms SelectedHolomorphicSignCoordinate318.same_scaled_abscissa
#print axioms SelectedHolomorphicSignCoordinate318.continuous_coordinates
