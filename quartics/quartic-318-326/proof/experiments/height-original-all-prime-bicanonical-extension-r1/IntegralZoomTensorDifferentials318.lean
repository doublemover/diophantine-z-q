module
public import IntegralContactZoomCoefficients318
public section
noncomputable section
namespace IntegralZoomTensorDifferentials318
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1400000
variable {V : Type*} [CommRing V] (α β γ : Fin 4 → V) (t : V)
theorem frame_D_newCoordinate : IntegralZoomNeighborhood318.frame V α β γ t
    (KaehlerDifferential.D V _ (IntegralZoomNeighborhood318.newCoordinate V α β γ t))=1 := by
  letI : Algebra.Etale V[X] (IntegralZoomNeighborhood318.Chart V α β γ t) :=
    IntegralZoomNeighborhood318.etale V α β γ t
  unfold IntegralZoomNeighborhood318.frame IntegralZoomNeighborhood318.newCoordinate
  rw [LocalizedKaehlerFrame318.etaleFrame_D,KaehlerDifferential.polynomialEquiv_D,
    derivative_X,map_one]

theorem D_oldCoordinate : KaehlerDifferential.D V _
    (IntegralZoomNeighborhood318.oldCoordinate V α β γ t)=
      algebraMap V (IntegralZoomNeighborhood318.Chart V α β γ t)
        (IntegralQuadraticPointZoom318.scale α β γ t) •
      KaehlerDifferential.D V _ (IntegralZoomNeighborhood318.newCoordinate V α β γ t) := by
  apply (IntegralZoomNeighborhood318.frame V α β γ t).injective
  rw [IntegralZoomNeighborhood318.frame_D_oldCoordinate,map_smul,frame_D_newCoordinate,
    smul_eq_mul,mul_one]

open IntegralContactZoomCoefficients318
variable (d a : Fin 4 → V) (m : Mode) (y : Fin 4 → V)
  (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value (alpha d a m) d (gamma d a m) t i)

theorem generic_q0_tensor_identity
    (hd : IsUnit (algebraMap V (Chart d a t m) (∏ i : Fin 4,d i))) :
    contactProduct d a t m • section0 d a t m=
      KaehlerDifferential.D V (Chart d a t m) (oldCoordinate d a t m) ⊗ₜ[Chart d a t m]
        KaehlerDifferential.D V (Chart d a t m) (oldCoordinate d a t m) := by
  rw [section0,←mul_smul,q0_generic_cleared d a t m y hy hd]
  simp only [D_oldCoordinate,TensorProduct.smul_tmul_smul,←pow_two]
  rfl

/-- Actual equality of tensor-square differentials follows after genuine
contact-polynomial unit cancellation on the generic noncontact open. -/
theorem generic_q0_unique
    (hd : IsUnit (algebraMap V (Chart d a t m) (∏ i : Fin 4,d i)))
    (hP : IsUnit (contactProduct d a t m))
    (s : Omega d a t m ⊗[Chart d a t m] Omega d a t m)
    (hs : contactProduct d a t m • s=
      KaehlerDifferential.D V (Chart d a t m) (oldCoordinate d a t m) ⊗ₜ[Chart d a t m]
        KaehlerDifferential.D V (Chart d a t m) (oldCoordinate d a t m)) :
    section0 d a t m=s := by
  apply hP.smul_left_cancel.mp
  exact (generic_q0_tensor_identity t d a m y hy hd).trans hs.symm
end IntegralZoomTensorDifferentials318
