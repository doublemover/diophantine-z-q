module

public import SelectedActualRationalMonicChartDifferential318
public import Mathlib.Analysis.Calculus.FDeriv.Congr

public section

noncomputable section

open Filter Polynomial
open scoped Topology

namespace SelectedActualRationalPeriodChartReadout318

open SelectedActualRationalDifferentialPeriodDerivation318
open SelectedActualRationalMonicChartDifferential318

private theorem evalDen_isUnit (j : ℂ) (hj : j ≠ 0 ∧ j ≠ 1728) :
    IsUnit (Polynomial.aeval j actualOrdinaryDenominator) := by
  have h : Polynomial.aeval j actualOrdinaryDenominator = j * (j - 1728) := by
    simp [actualOrdinaryDenominator]
  rw [h]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero hj.1 (sub_ne_zero.mpr hj.2))

/-- Evaluate the literal localized coefficient ring at the same chosen J. -/
def baseEval (j : ℂ) (hj : j ≠ 0 ∧ j ≠ 1728) : R →ₐ[ℚ] ℂ :=
  IsLocalization.Away.liftAlgHom actualOrdinaryDenominator
    (f := Polynomial.aeval j) (evalDen_isUnit j hj)

theorem baseEval_j (j : ℂ) (hj : j ≠ 0 ∧ j ≠ 1728) :
    baseEval j hj (algebraMap ℚ[X] R Polynomial.X) = j := by
  unfold baseEval
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq, Polynomial.aeval_X]

/-- The ordinary chart hom is constructed by the actual root
of the same p at the evaluated J and x, not given as separate data. -/
def chartEval (p : R[X]) (j x : ℂ) (hj : j ≠ 0 ∧ j ≠ 1728)
    (hp : p.eval₂ (baseEval j hj) x = 0) : A p →ₐ[ℚ] ℂ :=
  AdjoinRoot.liftAlgHom p (baseEval j hj) x hp

theorem chartEval_j (p : R[X]) (j x : ℂ) (hj : j ≠ 0 ∧ j ≠ 1728)
    (hp : p.eval₂ (baseEval j hj) x = 0) :
    chartEval p j x hj hp (parameter p) = j := by
  unfold chartEval parameter baseIntoRoot
  rw [RingHom.comp_apply, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of, baseEval_j]

theorem chartEval_x (p : R[X]) (j x : ℂ) (hj : j ≠ 0 ∧ j ≠ 1728)
    (hp : p.eval₂ (baseEval j hj) x = 0) :
    chartEval p j x hj hp (AdjoinRoot.root p) = x :=
  AdjoinRoot.liftAlgHom_root p (baseEval j hj) x hp

/-- The exact actual analytic graph of the original marked period, locally.
The only equation input is the literal monic relation already obtained on
the actual marked period coordinates. -/
structure PeriodGraph (p : R[X]) (τ : ℂ) where
  openSet : Set ℂ
  openSet_nhds : openSet ∈ 𝓝 τ
  j : ℂ → ℂ
  x : ℂ → ℂ
  denom : ∀ z ∈ openSet, j z ≠ 0 ∧ j z ≠ 1728
  rootRelation : ∀ z (hz : z ∈ openSet), p.eval₂ (baseEval (j z) (denom z hz)) (x z) = 0
  j_diff : DifferentiableAt ℂ j τ
  x_diff : DifferentiableAt ℂ x τ

variable {p : R[X]} {τ : ℂ}

/-- Totalize only outside the actual neighborhood: the jet is independent of
this padding, and the center is exactly the given original point. -/
def family (G : PeriodGraph p τ) (z : ℂ) : A p →ₐ[ℚ] ℂ := by
  classical
  exact if h : z ∈ G.openSet then
    chartEval p (G.j z) (G.x z) (G.denom z h) (G.rootRelation z h)
  else
    let hc : τ ∈ G.openSet := mem_of_mem_nhds G.openSet_nhds
    chartEval p (G.j τ) (G.x τ) (G.denom τ hc) (G.rootRelation τ hc)

theorem family_eq_of_mem (G : PeriodGraph p τ) (z : ℂ) (hz : z ∈ G.openSet) :
    family G z = chartEval p (G.j z) (G.x z) (G.denom z hz) (G.rootRelation z hz) := by
  unfold family
  exact dif_pos hz

theorem family_j_eventually (G : PeriodGraph p τ) :
    (fun z => family G z (parameter p)) =ᶠ[𝓝 τ] G.j := by
  filter_upwards [G.openSet_nhds] with z hz
  rw [family_eq_of_mem G z hz, chartEval_j]

theorem family_x_eventually (G : PeriodGraph p τ) :
    (fun z => family G z (AdjoinRoot.root p)) =ᶠ[𝓝 τ] G.x := by
  filter_upwards [G.openSet_nhds] with z hz
  rw [family_eq_of_mem G z hz, chartEval_x]

theorem family_differentiable (G : PeriodGraph p τ) :
    ∀ r : A p, DifferentiableAt ℂ (fun z => family G z r) τ :=
  differentiable_actual_monic_chart p (family G) τ
    (G.j_diff.congr_of_eventuallyEq (family_j_eventually G))
    (G.x_diff.congr_of_eventuallyEq (family_x_eventually G))

/-- The actual ordered period-frame value of a rational canonical
differential in the normalized ordinary dJ frame. This constructs
the coordinate evaluation and the pullback; there is no independently
supplied analytic coefficient and no division by the derivative. -/
theorem actual_period_coefficient (G : PeriodGraph p τ)
    (frame : KaehlerDifferential ℚ (A p) ≃ₗ[A p] A p)
    (hframe : frame (KaehlerDifferential.D ℚ (A p) (parameter p)) = 1)
    (ω : KaehlerDifferential ℚ (A p)) :
    letI : Algebra (A p) ℂ := (family G τ).toRingHom.toAlgebra
    letI : IsScalarTower ℚ (A p) ℂ :=
      IsScalarTower.of_algebraMap_eq (fun c => ((family G τ).commutes c).symm)
    (evaluationDerivation (family G) τ (family_differentiable G)).liftKaehlerDifferential ω =
      family G τ (frame ω) * deriv G.j τ := by
  letI : Algebra (A p) ℂ := (family G τ).toRingHom.toAlgebra
  letI : IsScalarTower ℚ (A p) ℂ :=
    IsScalarTower.of_algebraMap_eq (fun c => ((family G τ).commutes c).symm)
  have h₁ := pullback_normalized_differential (family G) τ (family_differentiable G)
    (parameter p) frame hframe ω
  exact h₁.trans (congrArg (fun d : ℂ => family G τ (frame ω) * d) (family_j_eventually G).deriv_eq)

end SelectedActualRationalPeriodChartReadout318

#print axioms SelectedActualRationalPeriodChartReadout318.family_differentiable
#print axioms SelectedActualRationalPeriodChartReadout318.actual_period_coefficient
