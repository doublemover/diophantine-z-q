module
public import OriginalFiniteZoomBranchMap318
public import OriginalBranchEvaluationExt318
public import ZoomChartPointAlgebra318
public section
noncomputable section
namespace FiniteZoomBranchPoint318
open Polynomial IntegralContactZoomCoefficients318 OriginalFiniteZoomBranchMap318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (havoid : ∀ j,RationalContactPoint318.parameters c t j≠0)
abbrev K := RationalContactPoint318.PointField c t
variable (d y s : Fin 4 → K c t) (τ : K c t)
  (hs : ∀ j,s j≠0) (hc : ∀ j,algebraMap ℚ (K c t) (c j : ℚ)=d j*(s j)^2)
  (hy : ∀ j,(y j)^2=IntegralQuadraticPointZoom318.value
    (alpha d (contacts (K:=K c t)) .finite) d (gamma d (contacts (K:=K c t)) .finite) τ j)
  (hn : ∀ j,y j≠0)
  (hτ : τ=algebraMap ℚ (K c t) t)
  (hr : ∀ j,s j*y j=RationalFourRootFiber318.root (RationalContactPoint318.parameters c t) j)
@[expose] def evaluation : Target d τ →ₐ[ℚ] K c t :=
  (ZoomChartPointAlgebra318.point (K c t) (alpha d (contacts (K:=K c t)) .finite)
    d (gamma d (contacts (K:=K c t)) .finite) τ).restrictScalars ℚ

include hτ in
theorem polynomial_evaluation : (evaluation c t d τ).toRingHom.comp (sourceScalar d τ)=
    (algebraMap ℚ (K c t)).comp (Polynomial.aeval t).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro q
    change evaluation c t d τ (Polynomial.eval₂ (algebraMap ℚ (Target d τ)) _ (C q))=_
    rw [Polynomial.eval₂_C,(evaluation c t d τ).commutes]
    change algebraMap ℚ _ q=algebraMap ℚ _ (Polynomial.aeval t (C q))
    rw [Polynomial.aeval_C]
  · change evaluation c t d τ (Polynomial.eval₂ (algebraMap ℚ (Target d τ)) _ X)=_
    rw [Polynomial.eval₂_X]
    change IntegralZoomNeighborhood318.point _ _ _ _ _ (IntegralZoomNeighborhood318.oldCoordinate _ _ _ _ _)=_
    rw [IntegralZoomNeighborhood318.point_oldCoordinate,hτ]
    change algebraMap ℚ _ t=algebraMap ℚ _ (Polynomial.aeval t X)
    rw [Polynomial.aeval_X]

include hτ hr in
theorem branch_point (i : Fin 4) : (evaluation c t d τ).toRingHom.comp
    (branchMap c d τ y s hs hc hy hn i).toRingHom=ContactBranchPoint318.branchPoint c t havoid i := by
  apply OriginalBranchEvaluationExt318.eq_original c t havoid i
  · intro p
    change evaluation c t d τ (branchRingMap c d τ y s hs hc hy hn i (algebraMap _ _ (algebraMap ℚ[X] _ p)))=_
    rw [branchRingMap_base,sourceMap_polynomial]
    exact RingHom.congr_fun (polynomial_evaluation c t d τ hτ) p
  · intro j
    change evaluation c t d τ (branchRingMap c d τ y s hs hc hy hn i (algebraMap _ _ (FourRootOrderSigns318.generator _ j)))=_
    rw [branchRingMap_base,sourceMap_generator,originalRoot,map_mul]
    change IntegralZoomNeighborhood318.point _ _ _ _ _ (algebraMap (K c t) _ (s j))*
      IntegralZoomNeighborhood318.point _ _ _ _ _ (IntegralZoomNeighborhood318.oldRoot _ _ _ _ _ y j)=_
    rw [IntegralZoomNeighborhood318.point_scalar,IntegralZoomNeighborhood318.point_oldRoot]
    exact hr j
end FiniteZoomBranchPoint318
