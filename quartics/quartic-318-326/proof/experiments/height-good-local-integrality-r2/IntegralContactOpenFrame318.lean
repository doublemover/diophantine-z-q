module
public import FourRootOrder318
public import LocalizedKaehlerFrame318
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace IntegralContactOpenFrame318
open Polynomial
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R]

@[expose] def contacts : Fin 4 → ℤ := ![0,32,76832,-343]
@[expose] def denominator : R[X] := ∏ i : Fin 4, (X - C (contacts i : R))
abbrev Base := Localization.Away (denominator R)
@[expose] def coefficient (c : Fin 4 → Rˣ) (i : Fin 4) : R[X] :=
  C (c i : R) * (X - C (contacts i : R))
abbrev Order (c : Fin 4 → Rˣ) :=
  FourRootOrder318.Order (fun i => algebraMap R[X] (Base R) (coefficient R c i))

-- Use the native quotient/tensor scalar actions and their compatible algebra
-- structures. A new RingHom.toAlgebra would replace the scalar action and
-- conflict with the existing tensor-product Module instances.
variable (c : Fin 4 → Rˣ)
theorem coefficient_unit (i : Fin 4) :
    IsUnit (algebraMap R[X] (Base R) (coefficient R c i)) := by
  rw [coefficient, map_mul]
  apply IsUnit.mul
  · exact ((c i).isUnit.map C).map (algebraMap R[X] (Base R))
  · apply IsLocalization.Away.isUnit_of_dvd (denominator R)
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- This is the actual four-root integral order over the complement of P=0.
No smoothness, differential frame or etaleness of this order is assumed. -/
theorem finite_free_etale (h2 : IsUnit (2 : R)) :
    Module.Finite (Base R) (Order R c) ∧ Module.Free (Base R) (Order R c) ∧
      Algebra.Etale (Base R) (Order R c) := by
  have hb : IsUnit (2 : Base R) := by
    simpa only [map_ofNat] using h2.map (algebraMap R (Base R))
  exact ⟨(FourRootOrder318.finite_free _).1, (FourRootOrder318.finite_free _).2,
    FourRootOrder318.etale _ hb (coefficient_unit R c)⟩

@[expose] def baseFrame : KaehlerDifferential R (Base R) ≃ₗ[Base R] Base R :=
  LocalizedKaehlerFrame318.localFrame (Submonoid.powers (denominator R))
    (KaehlerDifferential.polynomialEquiv R)

/-- An integral dt frame constructed on the entire actual noncontact chart. -/
@[expose] def frame (h2 : IsUnit (2 : R)) :
    KaehlerDifferential R (Order R c) ≃ₗ[Order R c] Order R c := by
  letI : Algebra.Etale (Base R) (Order R c) := (finite_free_etale R c h2).2.2
  exact LocalizedKaehlerFrame318.etaleFrame (baseFrame R)

@[expose] def coordinate : Order R c :=
  algebraMap (Base R) (Order R c) (algebraMap R[X] (Base R) X)

theorem frame_D (h2 : IsUnit (2 : R)) :
    frame R c h2 (KaehlerDifferential.D R (Order R c) (coordinate R c)) = 1 := by
  letI : Algebra.Etale (Base R) (Order R c) := (finite_free_etale R c h2).2.2
  change LocalizedKaehlerFrame318.etaleFrame (baseFrame R)
    (KaehlerDifferential.D R (Order R c) (algebraMap (Base R) (Order R c) _)) = 1
  rw [LocalizedKaehlerFrame318.etaleFrame_D]
  change algebraMap (Base R) (Order R c)
    (LocalizedKaehlerFrame318.localFrame (Submonoid.powers (denominator R))
      (KaehlerDifferential.polynomialEquiv R)
      (KaehlerDifferential.D R (Base R) (algebraMap R[X] (Base R) X))) = 1
  rw [LocalizedKaehlerFrame318.localFrame_D, KaehlerDifferential.polynomialEquiv_D,
    Polynomial.derivative_X, map_one, map_one]

-- Localization already carries the compatible scalar actions and scalar
-- towers inherited from the original order. Do not replace its algebra by
-- a fresh RingHom.toAlgebra with a different definitional scalar action.
-- Resolve the native differential module at abstract rings first. Its scalar
-- action is exactly the derived Kaehler action, not a new toAlgebra action.
private abbrev nativeCotangentModule (A T : Type*) [CommRing A] [CommRing T]
    [Algebra A T] : Module T (KaehlerDifferential A T) := inferInstance

local instance primeCotangentModule (P : Ideal (Order R c)) [P.IsPrime] :
    Module (Localization.AtPrime P) (KaehlerDifferential R (Localization.AtPrime P)) :=
  nativeCotangentModule R (Localization.AtPrime P)

/-- The source local frame remains available at every actual prime of this
chart, not only after passage to its generic fiber. -/
@[expose] def atPrimeFrame (h2 : IsUnit (2 : R)) (P : Ideal (Order R c)) [P.IsPrime] :
    KaehlerDifferential R (Localization.AtPrime P) ≃ₗ[Localization.AtPrime P]
      Localization.AtPrime P :=
  LocalizedKaehlerFrame318.localFrame P.primeCompl (frame R c h2)

theorem atPrimeFrame_D (h2 : IsUnit (2 : R)) (P : Ideal (Order R c)) [P.IsPrime] :
    atPrimeFrame R c h2 P (KaehlerDifferential.D R (Localization.AtPrime P)
      (algebraMap (Order R c) (Localization.AtPrime P) (coordinate R c))) = 1 :=
  LocalizedKaehlerFrame318.localFrame_normalized P.primeCompl (frame R c h2)
    (coordinate R c) (frame_D R c h2)

end IntegralContactOpenFrame318
