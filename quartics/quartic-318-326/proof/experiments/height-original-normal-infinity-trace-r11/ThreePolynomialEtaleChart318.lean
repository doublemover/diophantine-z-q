module
public import IntegralRootPointMaps318
public import LocalizedKaehlerFrame318
public import Mathlib.RingTheory.RingHom.Smooth
public section
noncomputable section
namespace ThreePolynomialEtaleChart318
open Polynomial
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable (V : Type*) [CommRing V] (q : Fin 3 → V[X])
@[expose] def denominator : V[X] := ∏ j : Fin 3,q j
abbrev Base := Localization.Away (denominator V q)
abbrev Chart := ThreeRootOrder318.Order (fun j => algebraMap V[X] (Base V q) (q j))
@[expose] def coordinate : Chart V q :=
  algebraMap (Base V q) (Chart V q) (algebraMap V[X] (Base V q) X)
@[expose] def polynomial (p : V[X]) : Chart V q :=
  algebraMap (Base V q) (Chart V q) (algebraMap V[X] (Base V q) p)

theorem coefficient_unit (j : Fin 3) : IsUnit (algebraMap V[X] (Base V q) (q j)) :=
  IsLocalization.Away.isUnit_of_dvd (denominator V q)
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
theorem etale (h2 : IsUnit (2 : V)) : Algebra.Etale (Base V q) (Chart V q) :=
  ThreeRootOrder318.etale _
    (by simpa only [map_ofNat] using h2.map (algebraMap V (Base V q)))
    (coefficient_unit V q)
theorem smooth (h2 : IsUnit (2 : V)) : Algebra.Smooth V (Chart V q) := by
  letI : Algebra.Smooth V V[X] := ⟨inferInstance,inferInstance⟩
  letI : Algebra.Smooth V[X] (Base V q) := Algebra.Smooth.of_isLocalization_Away (denominator V q)
  letI : Algebra.Smooth V (Base V q) := Algebra.Smooth.comp V V[X] (Base V q)
  letI : Algebra.Etale (Base V q) (Chart V q) := etale V q h2
  exact Algebra.Smooth.comp V (Base V q) (Chart V q)
@[expose] def frame (h2 : IsUnit (2 : V)) :
    KaehlerDifferential V (Chart V q) ≃ₗ[Chart V q] Chart V q := by
  letI : Algebra.Etale (Base V q) (Chart V q) := etale V q h2
  exact LocalizedKaehlerFrame318.etaleFrame
    (LocalizedKaehlerFrame318.localFrame (Submonoid.powers (denominator V q))
      (KaehlerDifferential.polynomialEquiv V))
theorem frame_polynomial (h2 : IsUnit (2 : V)) (p : V[X]) :
    frame V q h2 (KaehlerDifferential.D V _ (polynomial V q p)) =
      polynomial V q p.derivative := by
  letI : Algebra.Etale (Base V q) (Chart V q) := etale V q h2
  unfold frame polynomial
  rw [LocalizedKaehlerFrame318.etaleFrame_D,LocalizedKaehlerFrame318.localFrame_D,
    KaehlerDifferential.polynomialEquiv_D]
theorem coordinate_normalized (h2 : IsUnit (2 : V)) :
    frame V q h2 (KaehlerDifferential.D V _ (coordinate V q))=1 := by
  change frame V q h2 (KaehlerDifferential.D V _ (polynomial V q X))=1
  rw [frame_polynomial,derivative_X]
  simp only [polynomial,map_one]

variable (Z : V) (r : Fin 3 → Vˣ)
  (hr : ∀ j,(r j : V)^2=Polynomial.eval Z (q j))
include hr in
theorem denominator_unit : IsUnit (Polynomial.eval Z (denominator V q)) := by
  simp only [denominator,eval_prod]
  exact IsUnit.prod_univ_iff.mpr (fun j => (hr j) ▸ (r j).isUnit.pow 2)
@[expose] def basePoint : Base V q →+* V :=
  IsLocalization.Away.lift (denominator V q) (denominator_unit V q Z r hr)
theorem basePoint_polynomial (p : V[X]) :
    basePoint V q Z r hr (algebraMap V[X] (Base V q) p)=Polynomial.eval Z p :=
  IsLocalization.Away.lift_eq _ _ _
@[expose] def point : Chart V q →+* V := by
  letI : Algebra (Base V q) V := (basePoint V q Z r hr).toAlgebra
  exact (IntegralRootPointMaps318.threeMap _ (fun j => (r j : V)) (fun j => by
    change (r j : V)^2=basePoint V q Z r hr _
    rw [basePoint_polynomial]
    exact hr j)).toRingHom

theorem point_polynomial (p : V[X]) : point V q Z r hr (polynomial V q p)=Polynomial.eval Z p := by
  letI : Algebra (Base V q) V := (basePoint V q Z r hr).toAlgebra
  have he (j : Fin 3) : (r j : V)^2=algebraMap (Base V q) V
      (algebraMap V[X] (Base V q) (q j)) := by
    change (r j : V)^2=basePoint V q Z r hr _
    rw [basePoint_polynomial]
    exact hr j
  exact ((IntegralRootPointMaps318.threeMap _ (fun j => (r j : V)) he).commutes _).trans
    (basePoint_polynomial V q Z r hr p)
theorem point_coordinate : point V q Z r hr (coordinate V q)=Z := by
  rw [show coordinate V q=polynomial V q X from rfl,point_polynomial,eval_X]
theorem point_scalar (k : V) : point V q Z r hr (algebraMap V (Chart V q) k)=k := by
  have hC : polynomial V q (C k)=algebraMap V (Chart V q) k :=
    (IsScalarTower.algebraMap_apply V[X] (Base V q) (Chart V q) (C k)).symm.trans
      (IsScalarTower.algebraMap_apply V V[X] (Chart V q) k).symm
  rw [←hC,point_polynomial,eval_C]
theorem point_root (j : Fin 3) : point V q Z r hr (ThreeRootCoordinates318.generator _ j)=(r j : V) := by
  letI : Algebra (Base V q) V := (basePoint V q Z r hr).toAlgebra
  have he (k : Fin 3) : (r k : V)^2=algebraMap (Base V q) V
      (algebraMap V[X] (Base V q) (q k)) := by
    change (r k : V)^2=basePoint V q Z r hr _
    rw [basePoint_polynomial]
    exact hr k
  exact IntegralRootPointMaps318.threeMap_generator _ _ he j
end ThreePolynomialEtaleChart318
