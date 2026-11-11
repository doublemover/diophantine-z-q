module
public import IntegralZoomProductUnits318
public import ZoomBicanonicalCancellation318
public section
noncomputable section
namespace IntegralContactZoomCoefficients318
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [CommRing V] (d a : Fin 4 → V) (t : V)
inductive Mode | finite | reciprocal
@[expose] def alpha : Mode → Fin 4 → V
  | .finite => fun _ => 0
  | .reciprocal => fun i => -d i*a i
@[expose] def gamma : Mode → Fin 4 → V
  | .finite => fun i => -d i*a i
  | .reciprocal => fun _ => 0
variable (m : Mode)
abbrev Chart := IntegralZoomNeighborhood318.Chart V (alpha d a m) d (gamma d a m) t
abbrev oldCoordinate := IntegralZoomNeighborhood318.oldCoordinate V (alpha d a m) d (gamma d a m) t
@[expose] def contactFactor (i : Fin 4) : Chart d a t m := match m with
  | .finite => oldCoordinate d a t .finite-algebraMap V _ (a i)
  | .reciprocal => 1-algebraMap V _ (a i)*oldCoordinate d a t .reciprocal
@[expose] def contactProduct : Chart d a t m := ∏ i : Fin 4,contactFactor d a t m i
@[expose] def weight : Chart d a t m := match m with
  | .finite => 1
  | .reciprocal => (oldCoordinate d a t .reciprocal)^4
@[expose] def commonCoefficient : Chart d a t m :=
  IntegralZoomProductUnits318.commonCoefficient (alpha d a m) d (gamma d a m) t d
@[expose] def q0 : Chart d a t m := commonCoefficient d a t m*weight d a t m
@[expose] def q1 : Chart d a t m := match m with
  | .finite => oldCoordinate d a t .finite*q0 d a t .finite
  | .reciprocal => commonCoefficient d a t .reciprocal*(oldCoordinate d a t .reciprocal)^3

variable (y : Fin 4 → V)
  (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value (alpha d a m) d (gamma d a m) t i)
include hy in
theorem original_root_square (i : Fin 4) :
    (IntegralZoomNeighborhood318.oldRoot V (alpha d a m) d (gamma d a m) t y i)^2=
      algebraMap V (Chart d a t m) (d i)*
        (match m with | .finite => 1 | .reciprocal => oldCoordinate d a t .reciprocal)*
          contactFactor d a t m i := by
  rw [IntegralZoomNeighborhood318.original_root_equation _ _ _ _ _ y hy i]
  cases m <;> simp only [IntegralZoomNeighborhood318.oldScalar,
    IntegralZoomNeighborhood318.oldCoefficient,coe_eval₂RingHom,eval₂_add,eval₂_mul,
    eval₂_pow,eval₂_C,eval₂_X,alpha,gamma,map_zero,map_neg,map_mul,contactFactor,
    zero_mul,zero_add,add_zero,mul_one] <;> ring

include hy in
theorem original_product_square :
    (∏ i : Fin 4,IntegralZoomNeighborhood318.oldRoot V (alpha d a m) d (gamma d a m) t y i)^2=
    algebraMap V (Chart d a t m) (∏ i : Fin 4,d i)*weight d a t m*contactProduct d a t m := by
  rw [Finset.prod_pow]
  simp only [original_root_square d a t m y hy,Finset.prod_mul_distrib,←map_prod,
    contactProduct]
  cases m <;> simp only [weight,Finset.prod_const,Finset.card_univ,Fintype.card_fin,one_pow]

include hy in
theorem q0_cleared :
    algebraMap V (Chart d a t m) (∏ i : Fin 4,d i)*contactProduct d a t m*q0 d a t m=
    algebraMap V (Chart d a t m) (∏ i : Fin 4,d i)*
      (algebraMap V (Chart d a t m)
        (IntegralQuadraticPointZoom318.scale (alpha d a m) d (gamma d a m) t))^2 := by
  have h := IntegralZoomProductUnits318.common_coefficient_identity
    (alpha d a m) d (gamma d a m) t y hy d
  rw [original_product_square d a t m y hy] at h
  calc
    _ = algebraMap V (Chart d a t m) (∏ i : Fin 4,d i)*weight d a t m*
      contactProduct d a t m*commonCoefficient d a t m := by unfold q0; ring
    _ = _ := h

include hy in
theorem q0_generic_cleared (hd : IsUnit (algebraMap V (Chart d a t m) (∏ i : Fin 4,d i))) :
    contactProduct d a t m*q0 d a t m=
      (algebraMap V (Chart d a t m)
        (IntegralQuadraticPointZoom318.scale (alpha d a m) d (gamma d a m) t))^2 := by
  apply ZoomBicanonicalCancellation318.cancel_coefficient hd.unit
  simpa only [hd.unit_spec] using q0_cleared d a t m y hy

theorem reciprocal_q1 : oldCoordinate d a t .reciprocal*q1 d a t .reciprocal=
    q0 d a t .reciprocal := by
  simp only [q1,q0,weight]
  ring

/-- These are genuine integral sections of the tensor square of the
actual relative Kaehler module of the constructed smooth chart. -/
abbrev Omega := KaehlerDifferential V (Chart d a t m)
@[expose] def coordinateSquare : Omega d a t m ⊗[Chart d a t m] Omega d a t m :=
  KaehlerDifferential.D V (Chart d a t m)
      (IntegralZoomNeighborhood318.newCoordinate V (alpha d a m) d (gamma d a m) t) ⊗ₜ[Chart d a t m]
    KaehlerDifferential.D V (Chart d a t m)
      (IntegralZoomNeighborhood318.newCoordinate V (alpha d a m) d (gamma d a m) t)
@[expose] def section0 : Omega d a t m ⊗[Chart d a t m] Omega d a t m :=
  q0 d a t m • coordinateSquare d a t m
@[expose] def section1 : Omega d a t m ⊗[Chart d a t m] Omega d a t m :=
  q1 d a t m • coordinateSquare d a t m

theorem finite_section_ratio : section1 d a t .finite=
    oldCoordinate d a t .finite • section0 d a t .finite := by
  rw [section1,section0,q1,mul_smul]
theorem reciprocal_section_ratio : oldCoordinate d a t .reciprocal • section1 d a t .reciprocal=
    section0 d a t .reciprocal := by
  rw [section1,section0,←mul_smul,reciprocal_q1]
end IntegralContactZoomCoefficients318
