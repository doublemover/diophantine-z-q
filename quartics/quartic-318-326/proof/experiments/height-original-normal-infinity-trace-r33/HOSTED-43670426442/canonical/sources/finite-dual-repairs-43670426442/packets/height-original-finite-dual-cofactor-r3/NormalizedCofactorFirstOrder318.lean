module
public import DVRNormalizedFiniteOrder318
public import IntegralRootPointMaps318
public import RingValuedCotangentEvaluation318
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public section
noncomputable section
namespace NormalizedCofactorFirstOrder318
open Polynomial
open scoped TensorProduct
variable (V : Type*) [CommRing V]
  (d a : Fin 4 → V) (T : V) (z : Fin 4 → V)
  (hz : ∀ i,(z i)^2=d i*(T-a i))
local notation "A" => DVRNormalizedFiniteOrder318.Order V d a
local notation "p" => DVRNormalizedFiniteOrder318.coefficient V d a

/-- The ACTUAL Jacobian minor for the four quadratic root equations.
It is retained as an integral scalar, never assumed to be a unit. -/
@[expose] def factor : V := ∏ i : Fin 4,2*z i

/-- The literal root-variable block of the four quadratic equation
Jacobian at the actual integral root values. -/
@[expose] def rootJacobian : Matrix (Fin 4) (Fin 4) V := Matrix.diagonal (fun i => 2*z i)

theorem determinant : Matrix.det (rootJacobian V z)=factor V z := Matrix.det_diagonal (d := fun i => 2*z i)

/-- The corresponding signed root-coordinate cofactor. -/
@[expose] def slope (i : Fin 4) : V := d i*∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,2*z j

theorem cofactor_relation (i : Fin 4) :
    z i*slope V d z i+slope V d z i*z i=d i*factor V z := by
  have hp := Finset.prod_erase_mul (Finset.univ : Finset (Fin 4)) (fun j => 2*z j) (Finset.mem_univ i)
  calc
    z i*slope V d z i+slope V d z i*z i=
        d i*((∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,2*z j)*(2*z i)) := by
      unfold slope
      ring
    _=d i*factor V z := congrArg (fun x : V => d i*x) hp

@[expose] def parameter : TrivSqZeroExt V V := (T,factor V z)
@[expose] def rootJet (i : Fin 4) : TrivSqZeroExt V V := (z i,slope V d z i)

include hz in
theorem root_relation (i : Fin 4) :
    rootJet V d z i^2=Polynomial.aeval (parameter V T z) (p i) := by
  simp only [DVRNormalizedFiniteOrder318.coefficient,map_mul,map_sub,
    Polynomial.aeval_C,Polynomial.aeval_X]
  rw [pow_two]
  apply TrivSqZeroExt.ext
  · change z i*z i=d i*(T-a i)
    exact (pow_two (z i)).symm.trans (hz i)
  · change z i*slope V d z i+slope V d z i*z i=
      d i*(factor V z-0)+0*(T-a i)
    rw [cofactor_relation]
    ring

/-- Integral first-order map on the WHOLE normalized order at arbitrary
nonunit twists, root values and residue characteristic. No inverse is used. -/
@[expose] def lift : A →ₐ[V] TrivSqZeroExt V V := by
  letI : Algebra V[X] (TrivSqZeroExt V V) :=
    (Polynomial.aeval (parameter V T z)).toRingHom.toAlgebra
  let F := IntegralRootPointMaps318.fourMap p (rootJet V d z) (root_relation V d a T z hz)
  exact { F.toRingHom with
    commutes' := fun r => by
      rw [IsScalarTower.algebraMap_apply V V[X] A]
      change F (algebraMap V[X] A (C r))=algebraMap V _ r
      exact (F.commutes (C r)).trans (Polynomial.aeval_C _ _) }

theorem lift_polynomial (q : V[X]) :
    lift V d a T z hz (algebraMap V[X] A q)=Polynomial.aeval (parameter V T z) q := by
  letI : Algebra V[X] (TrivSqZeroExt V V) :=
    (Polynomial.aeval (parameter V T z)).toRingHom.toAlgebra
  exact (IntegralRootPointMaps318.fourMap p (rootJet V d z) (root_relation V d a T z hz)).commutes q

theorem lift_root (i : Fin 4) :
    lift V d a T z hz (FourRootOrderSigns318.generator p i)=rootJet V d z i := by
  letI : Algebra V[X] (TrivSqZeroExt V V) :=
    (Polynomial.aeval (parameter V T z)).toRingHom.toAlgebra
  exact IntegralRootPointMaps318.fourMap_generator p (rootJet V d z) (root_relation V d a T z hz) i

variable (f : A →ₐ[V] V)
  (hf : ∀ q : V[X],f (algebraMap V[X] A q)=Polynomial.eval T q)
  (hr : ∀ i,f (FourRootOrderSigns318.generator p i)=z i)

include hf hr in
theorem projection (x : A) : (lift V d a T z hz x).fst=f x := by
  have h : (TrivSqZeroExt.fstHom V V V).toRingHom.comp (lift V d a T z hz).toRingHom=f.toRingHom := by
    apply IntegralRootPointMaps318.four_ringHom_ext
    · apply RingHom.ext
      intro q
      change (lift V d a T z hz (algebraMap V[X] A q)).fst=f (algebraMap V[X] A q)
      rw [lift_polynomial,hf]
      change (Polynomial.aeval (parameter V T z) q).fst=Polynomial.aeval T q
      exact (Polynomial.aeval_algHom_apply (TrivSqZeroExt.fstHom V V V) (parameter V T z) q).symm
    · intro i
      change (lift V d a T z hz (FourRootOrderSigns318.generator p i)).fst=_
      rw [lift_root,hr]
      rfl
  exact RingHom.congr_fun h x

/-- Native integral Jacobian-cofactor evaluation on the full integral
cotangent fiber. Identification with a dualizing sheaf is NOT assumed here. -/
@[expose] def evaluation :
    letI : Algebra A V := f.toRingHom.toAlgebra
    V ⊗[A] KaehlerDifferential V A →ₗ[V] V :=
  RingValuedCotangentEvaluation318.integralFiberMap V A V f (lift V d a T z hz)
    (projection V d a T z hz f hf hr)

theorem evaluation_dT :
    letI : Algebra A V := f.toRingHom.toAlgebra
    evaluation V d a T z hz f hf hr
      ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A (algebraMap V[X] A X))=factor V z := by
  letI : Algebra A V := f.toRingHom.toAlgebra
  rw [evaluation,RingValuedCotangentEvaluation318.integralFiberMap_differential,
    lift_polynomial,Polynomial.aeval_X]
  rfl

theorem evaluation_dRoot (i : Fin 4) :
    letI : Algebra A V := f.toRingHom.toAlgebra
    evaluation V d a T z hz f hf hr
      ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A (FourRootOrderSigns318.generator p i))=slope V d z i := by
  letI : Algebra A V := f.toRingHom.toAlgebra
  rw [evaluation,RingValuedCotangentEvaluation318.integralFiberMap_differential,lift_root]
  rfl
end NormalizedCofactorFirstOrder318
