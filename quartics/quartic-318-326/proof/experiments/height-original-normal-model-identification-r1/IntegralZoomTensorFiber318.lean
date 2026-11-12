module
public import IntegralZoomPointCoefficient318
public import IntegralZoomTensorDifferentials318
public section
noncomputable section
namespace IntegralZoomTensorFiber318
open IntegralContactZoomCoefficients318
open scoped TensorProduct
set_option maxHeartbeats 1400000
variable {V : Type*} [CommRing V] (d a : Fin 4 → V) (t : V) (m : Mode)
abbrev A := Chart d a t m
abbrev point := IntegralZoomPointCoefficient318.actualPoint t d a m
@[expose] def frame : Omega d a t m →ₛₗ[point d a t m] V where
  toFun ω := point d a t m (IntegralZoomNeighborhood318.frame V
    (alpha d a m) d (gamma d a m) t ω)
  map_add' ω η := by simp only [map_add]
  map_smul' r ω := by
    simp only [map_smul,smul_eq_mul,map_mul]

@[expose] def balanced : Omega d a t m →ₛₗ[point d a t m]
    Omega d a t m →ₛₗ[point d a t m] V where
  toFun ω :=
    { toFun := fun η => frame d a t m ω*frame d a t m η
      map_add' := fun η ξ => by rw [map_add,mul_add]
      map_smul' := fun r η => by
        rw [LinearMap.map_smulₛₗ]
        simp only [smul_eq_mul]
        ring }
  map_add' ω η := by
    ext ξ
    change frame d a t m (ω+η)*frame d a t m ξ=_
    rw [map_add,add_mul]
    rfl
  map_smul' r ω := by
    ext η
    change frame d a t m (r • ω)*frame d a t m η=
      point d a t m r • (frame d a t m ω*frame d a t m η)
    rw [LinearMap.map_smulₛₗ]
    simp only [smul_eq_mul]
    ring

/-- Evaluation of the genuine tensor square in the ACTUAL coordinate
frame at the actual integral section, with its exact scalar map. -/
@[expose] def tensorFiber : (Omega d a t m ⊗[A d a t m] Omega d a t m) →ₛₗ[point d a t m] V :=
  TensorProduct.lift (balanced d a t m)

theorem tensorFiber_tmul (ω η : Omega d a t m) :
    tensorFiber d a t m (ω ⊗ₜ[A d a t m] η)=frame d a t m ω*frame d a t m η :=
  TensorProduct.lift.tmul _ _ _

theorem frame_coordinate : frame d a t m
    (KaehlerDifferential.D V (A d a t m)
      (IntegralZoomNeighborhood318.newCoordinate V (alpha d a m) d (gamma d a m) t))=1 := by
  change point d a t m (IntegralZoomNeighborhood318.frame _ _ _ _ _ _)=1
  rw [IntegralZoomTensorDifferentials318.frame_D_newCoordinate,map_one]

theorem tensorFiber_coordinateSquare : tensorFiber d a t m (coordinateSquare d a t m)=1 := by
  rw [coordinateSquare,tensorFiber_tmul,frame_coordinate,mul_one]

theorem tensorFiber_section0 : tensorFiber d a t m (section0 d a t m)=
    IntegralZoomPointCoefficient318.fiber0 t d a m := by
  rw [section0,LinearMap.map_smulₛₗ,tensorFiber_coordinateSquare,smul_eq_mul,mul_one]
  rfl

theorem tensorFiber_section1 : tensorFiber d a t m (section1 d a t m)=
    IntegralZoomPointCoefficient318.fiber1 t d a m := by
  rw [section1,LinearMap.map_smulₛₗ,tensorFiber_coordinateSquare,smul_eq_mul,mul_one]
  rfl
end IntegralZoomTensorFiber318
