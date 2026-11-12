module
public import OriginalReciprocalZoomBranchMap318
public import OriginalMarkedBranchEvaluation318
public import ZoomChartPointAlgebra318
public section
noncomputable section
namespace ReciprocalZoomBranchPoint318
open Polynomial IntegralContactZoomCoefficients318 OriginalReciprocalZoomBranchMap318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (havoid : ∀ j,RationalContactPoint318.parameters c t j≠0)
abbrev K := RationalContactPoint318.PointField c t
variable (d y s : Fin 4 → K c t) (τ : K c t)
  (hs : ∀ j,s j≠0) (hc : ∀ j,algebraMap ℚ (K c t) (c j : ℚ)=d j*(s j)^2)
  (hy : ∀ j,(y j)^2=IntegralQuadraticPointZoom318.value
    (alpha d (contacts (K:=K c t)) .reciprocal) d (gamma d (contacts (K:=K c t)) .reciprocal) τ j)
  (hn : ∀ j,y j≠0)
  (hτ : τ=(algebraMap ℚ (K c t) t)⁻¹)
  (hr : ∀ j,s j*τ⁻¹*y j=RationalFourRootFiber318.root (RationalContactPoint318.parameters c t) j)
@[expose] def evaluation : Target d τ →ₐ[ℚ] K c t :=
  (ZoomChartPointAlgebra318.point (K c t) (alpha d (contacts (K:=K c t)) .reciprocal)
    d (gamma d (contacts (K:=K c t)) .reciprocal) τ).restrictScalars ℚ

theorem inverse_point : evaluation c t d τ (↑(coordinateUnit d τ y hy hn)⁻¹ : Target d τ)=τ⁻¹ := by
  have h := congrArg (evaluation c t d τ) (Units.mul_inv (coordinateUnit d τ y hy hn))
  rw [map_mul,map_one,coordinateUnit_val] at h
  have he : evaluation c t d τ (oldCoordinate d (contacts (K:=K c t)) τ .reciprocal)=τ :=
    IntegralZoomNeighborhood318.point_oldCoordinate _ _ _ _ _
  rw [he] at h
  have ht : τ≠0 := by
    intro hz
    rw [hz,zero_mul] at h
    exact zero_ne_one h
  apply (mul_left_cancel₀ ht)
  rw [h,mul_inv_cancel₀ ht]

include hr in
theorem original_root_point (j : Fin 4) :
    evaluation c t d τ (originalRoot d τ y s hy hn j)=
      RationalFourRootFiber318.root (RationalContactPoint318.parameters c t) j := by
  rw [originalRoot,map_mul,map_mul,inverse_point]
  change IntegralZoomNeighborhood318.point _ _ _ _ _ (algebraMap (K c t) _ (s j))*τ⁻¹*
    IntegralZoomNeighborhood318.point _ _ _ _ _ (IntegralZoomNeighborhood318.oldRoot _ _ _ _ _ y j)=_
  rw [IntegralZoomNeighborhood318.point_scalar,IntegralZoomNeighborhood318.point_oldRoot]
  exact hr j

/-- The reciprocal original branch is evaluated at the SAME original
signed point; inversion of the new coordinate is canceled literally. -/
include hτ hr in
theorem branch_point (i : Fin 4) : (evaluation c t d τ).toRingHom.comp
    (branchMap c d τ y s hs hc hy hn i).toRingHom=ContactBranchPoint318.branchPoint c t havoid i := by
  apply OriginalMarkedBranchEvaluation318.branch_point c t havoid
    (↑(coordinateUnit d τ y hy hn)⁻¹ : Target d τ)
    (originalRoot d τ y s hy hn) (originalRoot_equation c d τ y s hc hy hn)
    (originalRoot_unit d τ y s hs hy hn) (evaluation c t d τ)
  · rw [inverse_point,hτ,inv_inv]
  · exact original_root_point c t d y s τ hy hn hr
end ReciprocalZoomBranchPoint318
