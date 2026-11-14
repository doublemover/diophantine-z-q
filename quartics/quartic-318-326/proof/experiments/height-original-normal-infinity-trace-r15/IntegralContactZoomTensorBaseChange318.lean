module
public import IntegralContactZoomBaseChange318
public import BaseChangingDifferentialTensor318
public import FieldContactZoomTensor318
public section
noncomputable section
namespace IntegralContactZoomTensorBaseChange318
open IntegralContactZoomCoefficients318 IntegralContactZoomBaseChange318
open scoped TensorProduct
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {V K : Type*} [CommRing V] [Field K] [Algebra V K]
  (d a : Fin 4 → V) (t : V) (m : Mode) (y : Fin 4 → V)
  (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value (alpha d a m) d (gamma d a m) t i)
  (hn : ∀ i,algebraMap V K (y i)≠0)

include hy hn in
theorem coefficientMap_q0 : IntegralContactZoomBaseChange318.coefficientMap (S:=K) d a t m (q0 d a t m)=
    q0 (mapped (S:=K) d) (mapped (S:=K) a) (algebraMap V K t) m := by
  have hu := FieldContactZoomTensor318.coefficient_and_contact_units
    (mapped (S:=K) d) (mapped (S:=K) a) (algebraMap V K t) m (mapped (S:=K) y)
    (mapped_root_equation (S:=K) d a t m y hy) hn
  exact IntegralContactZoomBaseChange318.coefficientMap_q0 d a t m y hy hu.1 hu.2

include hy hn in
theorem coefficientMap_q1 : IntegralContactZoomBaseChange318.coefficientMap (S:=K) d a t m (q1 d a t m)=
    q1 (mapped (S:=K) d) (mapped (S:=K) a) (algebraMap V K t) m := by
  cases m with
  | finite =>
    rw [q1,map_mul,coefficientMap_oldCoordinate,coefficientMap_q0 d a t .finite y hy hn]
    rfl
  | reciprocal =>
    have hu := (FieldContactZoomTensor318.original_root_unit
      (mapped (S:=K) d) (mapped (S:=K) a) (algebraMap V K t) .reciprocal
      (mapped (S:=K) y) hn 0).pow 2
    rw [IntegralContactZoomCoefficients318.original_root_square
      (mapped (S:=K) d) (mapped (S:=K) a) (algebraMap V K t) .reciprocal
      (mapped (S:=K) y) (mapped_root_equation (S:=K) d a t .reciprocal y hy) 0] at hu
    have hU := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hu)
    have h := congrArg (IntegralContactZoomBaseChange318.coefficientMap (S:=K) d a t .reciprocal)
      (reciprocal_q1 d a t)
    rw [map_mul,coefficientMap_oldCoordinate,coefficientMap_q0 d a t .reciprocal y hy hn] at h
    apply hU.mul_left_cancel
    exact h.trans (reciprocal_q1 (mapped (S:=K) d) (mapped (S:=K) a) (algebraMap V K t)).symm

/-- This is the actual base-changing universal differential image of the
integral q0 coefficient and BOTH integral differential factors. -/
@[expose] def genericSection0 :
    Omega (mapped (S:=K) d) (mapped (S:=K) a) (algebraMap V K t) m ⊗[Changed (S:=K) d a t m]
      Omega (mapped (S:=K) d) (mapped (S:=K) a) (algebraMap V K t) m :=
  BaseChangingDifferentialTensor318.pureImage (S:=K)
    (IntegralContactZoomBaseChange318.coefficientMap (S:=K) d a t m) (q0 d a t m)
    (KaehlerDifferential.D V _ (IntegralZoomNeighborhood318.newCoordinate V (alpha d a m) d (gamma d a m) t))
    (KaehlerDifferential.D V _ (IntegralZoomNeighborhood318.newCoordinate V (alpha d a m) d (gamma d a m) t))

include hy hn in
theorem genericSection0_eq : genericSection0 (K:=K) d a t m=
    section0 (mapped (S:=K) d) (mapped (S:=K) a) (algebraMap V K t) m := by
  rw [genericSection0,BaseChangingDifferentialTensor318.pureImage_D,
    coefficientMap_q0 d a t m y hy hn,coefficientMap_coordinate]
  rfl
@[expose] def genericSection1 :
    Omega (mapped (S:=K) d) (mapped (S:=K) a) (algebraMap V K t) m ⊗[Changed (S:=K) d a t m]
      Omega (mapped (S:=K) d) (mapped (S:=K) a) (algebraMap V K t) m :=
  BaseChangingDifferentialTensor318.pureImage (S:=K)
    (IntegralContactZoomBaseChange318.coefficientMap (S:=K) d a t m) (q1 d a t m)
    (KaehlerDifferential.D V _ (IntegralZoomNeighborhood318.newCoordinate V (alpha d a m) d (gamma d a m) t))
    (KaehlerDifferential.D V _ (IntegralZoomNeighborhood318.newCoordinate V (alpha d a m) d (gamma d a m) t))

include hy hn in
theorem genericSection1_eq : genericSection1 (K:=K) d a t m=
    section1 (mapped (S:=K) d) (mapped (S:=K) a) (algebraMap V K t) m := by
  rw [genericSection1,BaseChangingDifferentialTensor318.pureImage_D,
    coefficientMap_q1 d a t m y hy hn,coefficientMap_coordinate]
  rfl
theorem tensorMap_section0 : BaseChangingDifferentialTensor318.tensorMap (S:=K)
    (IntegralContactZoomBaseChange318.coefficientMap (S:=K) d a t m) (section0 d a t m)=
      genericSection0 (K:=K) d a t m := by
  exact BaseChangingDifferentialTensor318.tensorMap_weighted _ _ _ _

theorem tensorMap_section1 : BaseChangingDifferentialTensor318.tensorMap (S:=K)
    (IntegralContactZoomBaseChange318.coefficientMap (S:=K) d a t m) (section1 d a t m)=
      genericSection1 (K:=K) d a t m := by
  exact BaseChangingDifferentialTensor318.tensorMap_weighted _ _ _ _

end IntegralContactZoomTensorBaseChange318
