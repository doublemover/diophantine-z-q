module
public import ThreeRootOrder318
public import LocalizedKaehlerFrame318
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace IntegralInfinityChart318
open Polynomial
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
@[expose] def contact : Fin 3 → R := ![32,76832,-343]
/-- The integral form of the original reciprocal radicand under u=c0/y0.
It divides only by the unit twist c0, never by a contact difference. -/
@[expose] def coefficient (j : Fin 3) : R[X] :=
  C ((c j.succ : R) * (↑(c 0)⁻¹ : R)) *
    (1 - C (contact R j * (↑(c 0)⁻¹ : R)) * X^2)
@[expose] def denominator : R[X] := ∏ j : Fin 3, coefficient R c j
abbrev Base := Localization.Away (denominator R c)
abbrev Order := ThreeRootOrder318.Order
  (fun j => algebraMap R[X] (Base R c) (coefficient R c j))

@[simp] theorem coefficient_at_zero (j : Fin 3) :
    Polynomial.eval 0 (coefficient R c j) = (c j.succ : R) * (↑(c 0)⁻¹ : R) := by
  simp [coefficient]

theorem denominator_at_zero_unit : IsUnit (Polynomial.eval 0 (denominator R c)) := by
  simp only [denominator,Polynomial.eval_prod,coefficient_at_zero]
  exact IsUnit.prod_univ_iff.mpr (fun j => (c j.succ).isUnit.mul ((c 0)⁻¹).isUnit)

/-- A genuine section of the infinity coordinate base at u=0, not a chosen
point of the full three-root source. -/
@[expose] def infinityBasePoint : Base R c →+* R :=
  IsLocalization.Away.lift (g := Polynomial.evalRingHom 0) (denominator R c)
    (denominator_at_zero_unit R c)

@[simp] theorem infinityBasePoint_on_polynomial (p : R[X]) :
    infinityBasePoint R c (algebraMap R[X] (Base R c) p) = Polynomial.eval 0 p :=
  IsLocalization.Away.lift_eq _ _ _

theorem coefficient_unit (j : Fin 3) :
    IsUnit (algebraMap R[X] (Base R c) (coefficient R c j)) :=
  IsLocalization.Away.isUnit_of_dvd (denominator R c)
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))

theorem finite_free_etale (h2 : IsUnit (2 : R)) :
    Module.Finite (Base R c) (Order R c) ∧ Module.Free (Base R c) (Order R c) ∧
      Algebra.Etale (Base R c) (Order R c) := by
  have h : IsUnit (2 : Base R c) := by simpa only [map_ofNat] using h2.map (algebraMap R (Base R c))
  exact ⟨(ThreeRootOrder318.finite_free _).1,(ThreeRootOrder318.finite_free _).2,
    ThreeRootOrder318.etale _ h (coefficient_unit R c)⟩

@[expose] def baseFrame : KaehlerDifferential R (Base R c) ≃ₗ[Base R c] Base R c :=
  LocalizedKaehlerFrame318.localFrame (Submonoid.powers (denominator R c))
    (KaehlerDifferential.polynomialEquiv R)
@[expose] def frame (h2 : IsUnit (2 : R)) :
    KaehlerDifferential R (Order R c) ≃ₗ[Order R c] Order R c := by
  letI : Algebra.Etale (Base R c) (Order R c) := (finite_free_etale R c h2).2.2
  exact LocalizedKaehlerFrame318.etaleFrame (baseFrame R c)
@[expose] def coordinate : Order R c :=
  algebraMap (Base R c) (Order R c) (algebraMap R[X] (Base R c) X)

theorem frame_D (h2 : IsUnit (2 : R)) :
    frame R c h2 (KaehlerDifferential.D R (Order R c) (coordinate R c)) = 1 := by
  letI : Algebra.Etale (Base R c) (Order R c) := (finite_free_etale R c h2).2.2
  change LocalizedKaehlerFrame318.etaleFrame (baseFrame R c)
    (KaehlerDifferential.D R _ (algebraMap _ _ _)) = 1
  rw [LocalizedKaehlerFrame318.etaleFrame_D]
  change algebraMap (Base R c) (Order R c)
    (LocalizedKaehlerFrame318.localFrame _ (KaehlerDifferential.polynomialEquiv R)
      (KaehlerDifferential.D R _ (algebraMap _ _ X))) = 1
  rw [LocalizedKaehlerFrame318.localFrame_D,KaehlerDifferential.polynomialEquiv_D,
    Polynomial.derivative_X,map_one,map_one]

@[expose] def inverseDenominator : Order R c :=
  algebraMap (Base R c) (Order R c) (IsLocalization.Away.invSelf (denominator R c))
@[expose] def orderDenominator : Order R c :=
  algebraMap R[X] (Order R c) (denominator R c)

theorem denominator_inverse : orderDenominator R c * inverseDenominator R c = 1 := by
  rw [orderDenominator,inverseDenominator,
    IsScalarTower.algebraMap_apply R[X] (Base R c) (Order R c),
    ←map_mul,IsLocalization.Away.mul_invSelf,map_one]

end IntegralInfinityChart318
