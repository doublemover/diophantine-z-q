module
public import OriginalZoomMarkedSectionComparison318
public import FiniteZoomBranchPoint318
public import ReciprocalZoomBranchPoint318
public section
noncomputable section
namespace OriginalZoomWholeBranchPoint318
open IntegralContactZoomCoefficients318
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (havoid : ∀ j,RationalContactPoint318.parameters c t j≠0)
abbrev K := RationalContactPoint318.PointField c t
variable (d a y s : Fin 4 → K c t) (τ : K c t) (m : Mode)
  (ha : a=fun j => algebraMap ℚ (K c t) (LinearContactSquareclass318.contacts j))
  (hs : ∀ j,s j≠0) (hc : ∀ j,algebraMap ℚ (K c t) (c j : ℚ)=d j*(s j)^2)
  (hy : ∀ j,(y j)^2=IntegralQuadraticPointZoom318.value (alpha d a m) d (gamma d a m) τ j)
  (hn : ∀ j,y j≠0)
@[expose] def evaluation : Chart d a τ m →ₐ[ℚ] K c t :=
  (ZoomChartPointAlgebra318.point (K c t) (alpha d a m) d (gamma d a m) τ).restrictScalars ℚ
@[expose] def originalRootValue (j : Fin 4) : K c t := match m with
  | .finite => s j*y j
  | .reciprocal => s j*τ⁻¹*y j
@[expose] def originalCoordinateValue : K c t := match m with
  | .finite => τ
  | .reciprocal => τ⁻¹

theorem whole_branch_point
    (hτ : τ=match m with | .finite => algebraMap ℚ (K c t) t | .reciprocal => (algebraMap ℚ (K c t) t)⁻¹)
    (hr : ∀ j,originalRootValue c t y s τ m j=
      RationalFourRootFiber318.root (RationalContactPoint318.parameters c t) j) (i : Fin 4) :
    (evaluation c t d a τ m).toRingHom.comp
      (OriginalZoomMarkedSectionComparison318.branchMap c d a τ m y s ha hs hc hy hn i).toRingHom=
        ContactBranchPoint318.branchPoint c t havoid i := by
  subst a
  cases m with
  | finite => exact FiniteZoomBranchPoint318.branch_point c t havoid d y s τ hs hc hy hn hτ hr i
  | reciprocal => exact ReciprocalZoomBranchPoint318.branch_point c t havoid d y s τ hs hc hy hn hτ hr i
end OriginalZoomWholeBranchPoint318
