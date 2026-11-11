module
public import IntegralZoomNeighborhood318
public import FourSimpleQuadraticUniversal318
public section
noncomputable section
namespace IntegralZoomProductUnits318
open scoped TensorProduct
set_option maxHeartbeats 1600000
variable {V : Type*} [CommRing V] (α β γ : Fin 4 → V) (t : V)
abbrev Chart := IntegralZoomNeighborhood318.Chart V α β γ t
@[expose] def derivativeUnit (i : Fin 4) : (Chart α β γ t)ˣ :=
  (FourSimpleQuadraticUniversal318.derivative_unit
    (IntegralZoomNeighborhood318.parameters V α β γ t) i).unit
@[expose] def productUnit : (Chart α β γ t)ˣ := ∏ i : Fin 4,derivativeUnit α β γ t i

theorem derivativeUnit_val (i : Fin 4) : (derivativeUnit α β γ t i : Chart α β γ t)=
    1+2*IntegralZoomNeighborhood318.generator V α β γ t i := by
  rw [derivativeUnit,IsUnit.unit_spec]
  exact add_comm _ _

theorem productUnit_val : (productUnit α β γ t : Chart α β γ t)=
    ∏ i : Fin 4,(1+2*IntegralZoomNeighborhood318.generator V α β γ t i) := by
  change (Units.valHom (Chart α β γ t)) (∏ i : Fin 4,derivativeUnit α β γ t i)=_
  rw [map_prod]
  exact Finset.prod_congr rfl (fun i _ => derivativeUnit_val α β γ t i)

variable (y : Fin 4 → V) (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value α β γ t i)
theorem root_product_square :
    (∏ i : Fin 4,IntegralZoomNeighborhood318.oldRoot V α β γ t y i)^2=
    algebraMap V (Chart α β γ t) (IntegralQuadraticPointZoom318.product α β γ t)*
      (productUnit α β γ t : Chart α β γ t)^2 := by
  rw [Finset.prod_pow]
  simp only [IntegralZoomNeighborhood318.oldRoot,mul_pow,←map_pow,hy,
    Finset.prod_mul_distrib,←map_prod,←Finset.prod_pow,←productUnit_val]
  rfl

/-- A literal integral coefficient on the actual all-prime smooth chart.
Only the actual derivative units are inverted, never2, the roots or delta. -/
@[expose] def commonCoefficient (d : Fin 4 → V) : Chart α β γ t :=
  16*algebraMap V (Chart α β γ t) (∏ i : Fin 4,d i)*
    algebraMap V (Chart α β γ t) (IntegralQuadraticPointZoom318.product α β γ t)*
      (↑(productUnit α β γ t)⁻¹ : Chart α β γ t)^2

theorem common_coefficient_identity (d : Fin 4 → V) :
    (∏ i : Fin 4,IntegralZoomNeighborhood318.oldRoot V α β γ t y i)^2*
      commonCoefficient α β γ t d=
    algebraMap V (Chart α β γ t) (∏ i : Fin 4,d i)*
      (algebraMap V (Chart α β γ t) (IntegralQuadraticPointZoom318.scale α β γ t))^2 := by
  rw [root_product_square α β γ t y hy]
  have hu : (productUnit α β γ t : Chart α β γ t)^2*
      (↑(productUnit α β γ t)⁻¹ : Chart α β γ t)^2=1 := by
    rw [←mul_pow,Units.mul_inv,one_pow]
  simp only [commonCoefficient,IntegralQuadraticPointZoom318.scale,map_mul,map_ofNat]
  calc
    _ = 16*algebraMap V (Chart α β γ t) (∏ i : Fin 4,d i)*
      (algebraMap V (Chart α β γ t) (IntegralQuadraticPointZoom318.product α β γ t))^2*
      ((productUnit α β γ t : Chart α β γ t)^2*
        (↑(productUnit α β γ t)⁻¹ : Chart α β γ t)^2) := by ring
    _ = _ := by rw [hu]; ring
end IntegralZoomProductUnits318
