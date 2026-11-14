module
public import OddTwistDilatationCoordinates318
public import LocalizedKaehlerFrame318
public import SquareCoordinateDifferential318
public import Mathlib.RingTheory.RingHom.Smooth
public section
noncomputable section
namespace OddTwistDilatationEtale318
open Polynomial OddTwistDilatationCoordinates318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (pi : V) (u : Vˣ) (a : V) (d b : Fin 3 → V)
@[expose] def denominator : V[X] := ∏ j : Fin 3, coefficient pi u a d b j
abbrev Base := Localization.Away (denominator V pi u a d b)
abbrev Chart := ThreeRootOrder318.Order (fun j =>
  algebraMap V[X] (Base V pi u a d b) (coefficient pi u a d b j))

theorem coefficient_unit (j : Fin 3) : IsUnit
    (algebraMap V[X] (Base V pi u a d b) (coefficient pi u a d b j)) :=
  IsLocalization.Away.isUnit_of_dvd (denominator V pi u a d b)
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))

/-- The whole localized dilatation chart is genuinely etale over its
polynomial parameter base at odd residue characteristic. There is no
assumption that the original singular four-root order was smooth. -/
theorem etale (h2 : IsUnit (2 : V)) :
    Algebra.Etale (Base V pi u a d b) (Chart V pi u a d b) :=
  ThreeRootOrder318.etale _
    (by simpa only [map_ofNat] using h2.map (algebraMap V (Base V pi u a d b)))
    (coefficient_unit V pi u a d b)

theorem smooth (h2 : IsUnit (2 : V)) : Algebra.Smooth V (Chart V pi u a d b) := by
  letI : Algebra.Smooth V V[X] := ⟨inferInstance,inferInstance⟩
  letI : Algebra.Smooth V[X] (Base V pi u a d b) :=
    Algebra.Smooth.of_isLocalization_Away (denominator V pi u a d b)
  letI : Algebra.Smooth V (Base V pi u a d b) :=
    Algebra.Smooth.comp V V[X] (Base V pi u a d b)
  letI : Algebra.Etale (Base V pi u a d b) (Chart V pi u a d b) := etale V pi u a d b h2
  exact Algebra.Smooth.comp V (Base V pi u a d b) (Chart V pi u a d b)

/-- A genuine free relative cotangent frame on this produced chart. It
is constructed by polynomial differential, actual localization and etale
base change, not by assigning a norm to an arbitrary field generator. -/
@[expose] def frame (h2 : IsUnit (2 : V)) :
    KaehlerDifferential V (Chart V pi u a d b) ≃ₗ[Chart V pi u a d b]
      Chart V pi u a d b := by
  letI : Algebra.Etale (Base V pi u a d b) (Chart V pi u a d b) := etale V pi u a d b h2
  exact LocalizedKaehlerFrame318.etaleFrame
    (LocalizedKaehlerFrame318.localFrame (Submonoid.powers (denominator V pi u a d b))
      (KaehlerDifferential.polynomialEquiv V))

@[expose] def coordinate : Chart V pi u a d b :=
  algebraMap (Base V pi u a d b) (Chart V pi u a d b)
    (algebraMap V[X] (Base V pi u a d b) X)
@[expose] def contactValue : Chart V pi u a d b :=
  algebraMap (Base V pi u a d b) (Chart V pi u a d b)
    (algebraMap V[X] (Base V pi u a d b) (contact pi u a))

theorem coordinate_normalized (h2 : IsUnit (2 : V)) :
    frame V pi u a d b h2 (KaehlerDifferential.D V _ (coordinate V pi u a d b)) = 1 := by
  letI : Algebra.Etale (Base V pi u a d b) (Chart V pi u a d b) := etale V pi u a d b h2
  unfold frame coordinate
  rw [LocalizedKaehlerFrame318.etaleFrame_D,LocalizedKaehlerFrame318.localFrame_D,
    KaehlerDifferential.polynomialEquiv_D,Polynomial.derivative_X,map_one,map_one]

theorem scalar_C (r : V) :
    algebraMap (Base V pi u a d b) (Chart V pi u a d b)
      (algebraMap V[X] (Base V pi u a d b) (C r)) =
        algebraMap V (Chart V pi u a d b) r :=
  (IsScalarTower.algebraMap_apply V[X] (Base V pi u a d b) (Chart V pi u a d b) (C r)).symm.trans
    (IsScalarTower.algebraMap_apply V V[X] (Chart V pi u a d b) r).symm

theorem contact_square : contactValue V pi u a d b -
    algebraMap V (Chart V pi u a d b) a =
    algebraMap V (Chart V pi u a d b) (pi*(↑u⁻¹ : V)) * (coordinate V pi u a d b)^2 := by
  simp only [contactValue,coordinate,contact,map_add,map_mul,map_pow,scalar_C]
  ring

/-- The true relative differential of the ORIGINAL contact parameter
has the uniformizer factor forced by the actual dilatation coordinate. -/
theorem frame_D_contact (h2 : IsUnit (2 : V)) :
    frame V pi u a d b h2 (KaehlerDifferential.D V _ (contactValue V pi u a d b)) =
      2 * algebraMap V (Chart V pi u a d b) (pi*(↑u⁻¹ : V)) * coordinate V pi u a d b :=
  SquareCoordinateDifferential318.frame_D_of_square (frame V pi u a d b h2)
    (contactValue V pi u a d b) (coordinate V pi u a d b) a (pi*(↑u⁻¹ : V))
    (contact_square V pi u a d b) (coordinate_normalized V pi u a d b h2)

variable (z : V) (r : Fin 3 → V)
  (hr : ∀ j, (r j)^2=Polynomial.eval z (coefficient pi u a d b j))
  (hunit : ∀ j, IsUnit (r j))

include hr hunit in
theorem denominator_value_unit : IsUnit (Polynomial.eval z (denominator V pi u a d b)) := by
  simp only [denominator,eval_prod]
  apply IsUnit.prod_univ_iff.mpr
  intro j
  rw [←hr j]
  exact (hunit j).pow 2

@[expose] def basePoint : Base V pi u a d b →+* V :=
  IsLocalization.Away.lift (denominator V pi u a d b)
    (denominator_value_unit V pi u a d b z r hr hunit)

theorem basePoint_polynomial (p : V[X]) :
    basePoint V pi u a d b z r hr hunit
      (algebraMap V[X] (Base V pi u a d b) p)=Polynomial.eval z p :=
  IsLocalization.Away.lift_eq _ _ _

@[expose] def point : Chart V pi u a d b →+* V := by
  letI : Algebra (Base V pi u a d b) V := (basePoint V pi u a d b z r hr hunit).toAlgebra
  exact (IntegralRootPointMaps318.threeMap _ r (fun j => by
    change (r j)^2 = basePoint V pi u a d b z r hr hunit
      (algebraMap V[X] (Base V pi u a d b) (coefficient pi u a d b j))
    rw [basePoint_polynomial]
    exact hr j)).toRingHom

theorem point_polynomial (p : V[X]) :
    point V pi u a d b z r hr hunit
      (algebraMap (Base V pi u a d b) (Chart V pi u a d b)
        (algebraMap V[X] (Base V pi u a d b) p)) = Polynomial.eval z p := by
  letI : Algebra (Base V pi u a d b) V := (basePoint V pi u a d b z r hr hunit).toAlgebra
  have he (j : Fin 3) : (r j)^2=algebraMap (Base V pi u a d b) V
      (algebraMap V[X] (Base V pi u a d b) (coefficient pi u a d b j)) := by
    change (r j)^2=basePoint V pi u a d b z r hr hunit _
    rw [basePoint_polynomial]
    exact hr j
  exact ((IntegralRootPointMaps318.threeMap _ r he).commutes _).trans
    (basePoint_polynomial V pi u a d b z r hr hunit p)

theorem point_scalar (k : V) :
    point V pi u a d b z r hr hunit (algebraMap V (Chart V pi u a d b) k)=k := by
  rw [←scalar_C V pi u a d b k,point_polynomial,Polynomial.eval_C]

theorem point_coordinate : point V pi u a d b z r hr hunit (coordinate V pi u a d b) = z := by
  rw [coordinate,point_polynomial,Polynomial.eval_X]

theorem point_contact : point V pi u a d b z r hr hunit (contactValue V pi u a d b) =
    Polynomial.eval z (contact pi u a) := point_polynomial V pi u a d b z r hr hunit _

theorem point_signed_root (j : Fin 3) : point V pi u a d b z r hr hunit
    (ThreeRootCoordinates318.generator _ j)=r j := by
  letI : Algebra (Base V pi u a d b) V := (basePoint V pi u a d b z r hr hunit).toAlgebra
  have he (k : Fin 3) : (r k)^2=algebraMap (Base V pi u a d b) V
      (algebraMap V[X] (Base V pi u a d b) (coefficient pi u a d b k)) := by
    change (r k)^2=basePoint V pi u a d b z r hr hunit _
    rw [basePoint_polynomial]
    exact hr k
  exact IntegralRootPointMaps318.threeMap_generator _ r he j
end OddTwistDilatationEtale318
