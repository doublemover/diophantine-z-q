module
public import IntegralZoomNeighborhood318
public section
noncomputable section
namespace ZoomChartPointAlgebra318
variable (K : Type*) [CommRing K] (α β γ : Fin 4 → K) (t : K)
@[expose] def point : IntegralZoomNeighborhood318.Chart K α β γ t →ₐ[K] K where
  __ := IntegralZoomNeighborhood318.point K α β γ t
  commutes' := IntegralZoomNeighborhood318.point_scalar K α β γ t

theorem point_old (i : Fin 4) (y : Fin 4 → K) :
    point K α β γ t (IntegralZoomNeighborhood318.oldRoot K α β γ t y i)=y i :=
  IntegralZoomNeighborhood318.point_oldRoot _ _ _ _ _ _ _

theorem point_coordinate : point K α β γ t (IntegralZoomNeighborhood318.oldCoordinate K α β γ t)=t :=
  IntegralZoomNeighborhood318.point_oldCoordinate _ _ _ _ _
end ZoomChartPointAlgebra318
