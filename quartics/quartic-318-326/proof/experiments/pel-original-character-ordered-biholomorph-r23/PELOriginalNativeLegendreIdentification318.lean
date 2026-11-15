module
public import PELOriginalDoubledPeriodSums318
public section
noncomputable section
namespace PELOriginalNativeLegendreIdentification318
open PELOriginalFourBranchCoordinate318 PELOriginalExactDoubledLattice318
open PELOriginalDoubledPeriodSums318
open scoped Topology Manifold ContDiff
variable (i:Fin 4)
local instance : Fact (branchParameter i≠0 ∧ branchParameter i≠1):=
  ⟨branchParameter_nonexceptional i⟩
local instance : (NormalizedLegendreProjectiveModel318.curve (branchParameter i)).IsElliptic:=
  NormalizedLegendreProjectiveModel318.curve_elliptic _
    (branchParameter_nonexceptional i).1 (branchParameter_nonexceptional i).2

/-- Actual source periods are TWICE the target lattice, so the original
source period cubic scales to the original Legendre curve by2*u, not u.
This factor is deduced from the genuine residual deck group, not degree. -/
@[expose] def scaling : ℂˣ:=
  Units.mk0 (2:ℂ) (by norm_num)*LegendreActualPeriodScaling318.scaling (branchParameter i)
lemma coefficients :
    NormalizedLegendreProjectiveModel318.A (branchParameter i)=(scaling i:ℂ)^4*
      OriginalPeriodProjectiveModel318.A (SourceLattice i) ∧
    NormalizedLegendreProjectiveModel318.B (branchParameter i)=(scaling i:ℂ)^6*
      OriginalPeriodProjectiveModel318.B (SourceLattice i) := by
  have h:=LegendreActualPeriodScaling318.scaling_spec (branchParameter i)
  constructor
  · rw [native_A_scale]
    change _=(2*(LegendreActualPeriodScaling318.scaling (branchParameter i):ℂ))^4*
      (OriginalPeriodProjectiveModel318.A (TargetLattice i)/16)
    rw [h.1]
    ring
  · rw [native_B_scale]
    change _=(2*(LegendreActualPeriodScaling318.scaling (branchParameter i):ℂ))^6*
      (OriginalPeriodProjectiveModel318.B (TargetLattice i)/64)
    rw [h.2]
    ring

/-- Original full-period native algebraic j equals the actual Legendre
j. This consumes the full-lattice coefficient bridge above, NOT a general
assertion that degree4-isogenous elliptic curves have equal j. -/
theorem native_j : (OriginalPeriodEllipticPoints318.curve (SourceLattice i)).j=
    (NormalizedLegendreProjectiveModel318.curve (branchParameter i)).j := by
  let u:=scaling i
  have h4:(NormalizedLegendreProjectiveModel318.curve (branchParameter i)).c₄=
      (u:ℂ)^4*(OriginalPeriodEllipticPoints318.curve (SourceLattice i)).c₄:=by
    rw [NormalizedLegendreProjectiveModel318.curve,NormalizedWeierstrass318.model_c4,
      OriginalPeriodEllipticPoints318.curve,NormalizedWeierstrass318.model_c4,
      (coefficients i).1]
    dsimp [OriginalPeriodProjectiveModel318.A]
    ring
  have hd:(NormalizedLegendreProjectiveModel318.curve (branchParameter i)).Δ=
      (u:ℂ)^12*(OriginalPeriodEllipticPoints318.curve (SourceLattice i)).Δ:=by
    rw [NormalizedLegendreProjectiveModel318.curve_discriminant,
      ←NormalizedLegendreProjectiveModel318.discriminant,
      (coefficients i).1,(coefficients i).2,
      OriginalPeriodEllipticPoints318.discriminant]
    dsimp [OriginalPeriodProjectiveModel318.A,OriginalPeriodProjectiveModel318.B]
    ring
  rw [WeierstrassCurve.j_eq,WeierstrassCurve.j_eq,h4,hd]
  have hn:(u:ℂ)^12≠0:=pow_ne_zero _ (Units.ne_zero u)
  have hnum:((u:ℂ)^4*(OriginalPeriodEllipticPoints318.curve (SourceLattice i)).c₄)^3=
      (u:ℂ)^12*(OriginalPeriodEllipticPoints318.curve (SourceLattice i)).c₄^3:=by ring
  rw [hnum,mul_div_mul_left _ _ hn]

/-- The exact published branch-parameter formula for the native source
curve, still with the actual original coordinate-character enumeration. -/
theorem native_j_formula : (OriginalPeriodEllipticPoints318.curve (SourceLattice i)).j=
    256*((branchParameter i)^2-branchParameter i+1)^3/
      ((branchParameter i)^2*(branchParameter i-1)^2) := by
  rw [native_j]
  exact NormalizedLegendreProjectiveModel318.curve_j _
    (branchParameter_nonexceptional i).1 (branchParameter_nonexceptional i).2

local instance : ChartedSpace ℂ (OriginalPeriodPlaneOverlap318.CompletedPlane (SourceLattice i)):=
  OriginalPeriodCompletedComplexAtlas318.chartedSpace (SourceLattice i)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OriginalPeriodPlaneOverlap318.CompletedPlane (SourceLattice i)):=
  OriginalPeriodCompletedComplexAtlas318.complex_manifold (SourceLattice i)
local instance : ChartedSpace ℂ (LegendrePlaneOverlap318.CompletedPlane (branchParameter i)):=
  LegendreCompletedComplexAtlas318.chartedSpace (branchParameter i)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (LegendrePlaneOverlap318.CompletedPlane (branchParameter i)):=
  LegendreCompletedComplexAtlas318.complex_manifold (branchParameter i)

/-- Concrete native coordinate scaling identifies the original period
cubic and actual Legendre cubic on BOTH charts and every completed point.
This is stronger than the numerical j identity and uses the same2*u. -/
@[expose] def comparison : OriginalPeriodPlaneOverlap318.CompletedPlane (SourceLattice i)≃ₜ
    LegendrePlaneOverlap318.CompletedPlane (branchParameter i):=
  LegendrePeriodScalingHolomorph318.comparison (SourceLattice i) (branchParameter i)
    (scaling i) (coefficients i).1 (coefficients i).2
lemma biholomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i).symm :=
  LegendrePeriodScalingHolomorph318.biholomorphic (SourceLattice i) (branchParameter i)
    (scaling i) (coefficients i).1 (coefficients i).2
end PELOriginalNativeLegendreIdentification318
