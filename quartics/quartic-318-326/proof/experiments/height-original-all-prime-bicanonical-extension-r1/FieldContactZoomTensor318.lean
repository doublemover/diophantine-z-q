module
public import IntegralZoomTensorDifferentials318
public section
noncomputable section
namespace FieldContactZoomTensor318
open IntegralContactZoomCoefficients318
open scoped TensorProduct
set_option maxHeartbeats 1600000
variable {K : Type*} [Field K] (d a : Fin 4 → K) (t : K) (m : Mode)
  (y : Fin 4 → K)
  (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value (alpha d a m) d (gamma d a m) t i)
  (hn : ∀ i,y i≠0)

theorem original_root_unit (i : Fin 4) : IsUnit
    (IntegralZoomNeighborhood318.oldRoot K (alpha d a m) d (gamma d a m) t y i) := by
  apply ((IsUnit.mk0 (y i) (hn i)).map (algebraMap K (Chart d a t m))).mul
  simpa only [add_comm] using FourSimpleQuadraticUniversal318.derivative_unit
    (IntegralZoomNeighborhood318.parameters K (alpha d a m) d (gamma d a m) t) i

theorem original_product_unit : IsUnit
    (∏ i : Fin 4,IntegralZoomNeighborhood318.oldRoot K (alpha d a m) d (gamma d a m) t y i) := by
  classical
  induction (Finset.univ : Finset (Fin 4)) using Finset.induction_on with
  | empty => simpa using (isUnit_one : IsUnit (1 : Chart d a t m))
  | @insert i s hi hs => rw [Finset.prod_insert hi]; exact (original_root_unit d a t m y hn i).mul hs

theorem coefficient_and_contact_units :
    IsUnit (algebraMap K (Chart d a t m) (∏ i : Fin 4,d i)) ∧
      IsUnit (contactProduct d a t m) := by
  have h := (original_product_unit d a t m y hn).pow 2
  rw [original_product_square d a t m y hy] at h
  exact ⟨isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h),isUnit_of_mul_isUnit_right h⟩

/-- The cleared q0 identity holds on the actual generic noncontact chart
without an extra coefficient-unit or contact-unit input. Both are produced
from the actual marked root units and the full product equation. -/
theorem q0_tensor_identity : contactProduct d a t m • section0 d a t m=
    KaehlerDifferential.D K (Chart d a t m) (oldCoordinate d a t m) ⊗ₜ[Chart d a t m]
      KaehlerDifferential.D K (Chart d a t m) (oldCoordinate d a t m) :=
  IntegralZoomTensorDifferentials318.generic_q0_tensor_identity t d a m y hy
    (coefficient_and_contact_units d a t m y hy hn).1

theorem q0_unique
    (s : Omega d a t m ⊗[Chart d a t m] Omega d a t m)
    (hs : contactProduct d a t m • s=
      KaehlerDifferential.D K (Chart d a t m) (oldCoordinate d a t m) ⊗ₜ[Chart d a t m]
        KaehlerDifferential.D K (Chart d a t m) (oldCoordinate d a t m)) :
    section0 d a t m=s :=
  IntegralZoomTensorDifferentials318.generic_q0_unique t d a m y hy
    (coefficient_and_contact_units d a t m y hy hn).1
    (coefficient_and_contact_units d a t m y hy hn).2 s hs
end FieldContactZoomTensor318
