module
public import LocalizedRootValueMonicDescent318
public import PELOriginalWholeChartNormal318
public section
noncomputable section
namespace PELOriginalBoundedFractionRegular318
open Polynomial ComplexPolynomialOpenPoints318
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
abbrev Base := MvPolynomial (Fin 2) ℂ
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- A fraction of the ACTUAL original whole chart is regular if its
actual monic localized equation has polynomially bounded root values on
EVERY base fiber. The source algebra, fraction embedding, and full base
map square are retained. This consumes proved whole-chart normality;
it does not assume the analytic function already defines a section. -/
theorem exists_regular
    (d : Base) (hd : d ≠ 0)
    (g : Base →+* CoordinateChart τ hτ j)
    (φ : Localization.Away d →+* FractionRing (CoordinateChart τ hτ j))
    (hφ : φ.comp (algebraMap Base (Localization.Away d)) =
      (algebraMap (CoordinateChart τ hτ j) (FractionRing (CoordinateChart τ hτ j))).comp g)
    (Q : Polynomial (Localization.Away d)) (hm : Q.Monic)
    (y : FractionRing (CoordinateChart τ hτ j)) (hy : Q.eval₂ φ y = 0)
    (m N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hroots : ∀ v (hv : MvPolynomial.eval v d ≠ 0), ∃ r : Fin m → ℂ,
      Q.map (evaluation d v hv) = ∏ i : Fin m, (X-Polynomial.C (r i)) ∧
      ∀ i, ‖r i‖ ≤ C*(1+‖v‖)^N) :
    ∃ a : CoordinateChart τ hτ j,
      algebraMap (CoordinateChart τ hτ j) (FractionRing (CoordinateChart τ hτ j)) a = y := by
  letI := PELOriginalWholeChartNormal318.integrallyClosed τ hτ j
  apply MonicGrowthIntegralFraction318.exists_regular d hd g φ hφ Q hm y hy
  intro n
  exact ⟨N*m,(1+C)^m,by positivity,fun v hv =>
    LocalizedRootValueMonicDescent318.coefficient_bound d Q m N C hC hroots n v hv⟩
end PELOriginalBoundedFractionRegular318
