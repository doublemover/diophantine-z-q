module
public import InfinityGlobalBase318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace ReciprocalOverlapBase318
open Polynomial
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Remove the already inverted factor from an iterated principal localization.
The conclusion uses the specified algebra structure, not an arbitrary ring iso. -/
theorem away_of_mul {R A B:Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (x q:R) [IsLocalization.Away q A] [IsLocalization.Away (x*q) B] :
    IsLocalization.Away (algebraMap R A x) B := by
  let T:=Localization.Away (algebraMap R A x)
  letI:IsLocalization.Away (x*q) T:=IsLocalization.Away.mul A T q x
  let e:T≃ₐ[R]B:=IsLocalization.algEquiv (Submonoid.powers (x*q)) T B
  let eA:T≃ₐ[A]B:=
    { e.toRingEquiv with
      commutes' := by
        have h:(e.toRingHom).comp (algebraMap A T)=algebraMap A B:=by
          apply IsLocalization.ringHom_ext (Submonoid.powers q)
          apply RingHom.ext
          intro r
          change e (algebraMap A T (algebraMap R A r))=algebraMap A B (algebraMap R A r)
          rw [←IsScalarTower.algebraMap_apply R A T,←IsScalarTower.algebraMap_apply R A B]
          exact e.commutes r
        exact RingHom.congr_fun h }
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap R A x)) eA

variable (c:Fin 4→ℚˣ)
abbrev R:=ℚ[X]
abbrev A:=ReciprocalInfinityBase318.ReciprocalOpen c
abbrev S:=ContactKummerOrder318.OpenBase
@[expose] def scalar : ℚ:=∏j:Fin 3,(c j.succ:ℚ)/(c 0:ℚ)

theorem scalar_ne_zero : scalar c≠0:=
  Finset.prod_ne_zero_iff.mpr (fun j _=>div_ne_zero (c j.succ).ne_zero (c 0).ne_zero)

theorem denominator_identity :
    X*ReciprocalInfinityBase318.reciprocalDenominator c=
      C (scalar c)*ContactReciprocalBase318.denominator:=by
  apply Polynomial.funext
  intro z
  simp [ReciprocalInfinityBase318.reciprocalDenominator,
    ReciprocalInfinityBase318.linearCoefficient,scalar,ContactReciprocalBase318.denominator,
    ContactReciprocalBase318.a,LinearContactSquareclass318.contacts,
    InfinityParameters318.contact,Fin.prod_univ_succ]
  <;> ring

local instance reciprocalAlgebra : Algebra R S:=(ContactReciprocalBase318.reciprocalPolynomial).toAlgebra
local instance reciprocalSMul : SMul R S:=reciprocalAlgebra.toSMul
local instance reciprocalModule : Module R S:=Algebra.toModule
local instance aSMul : SMul R (A c):=(inferInstance:Algebra R (A c)).toSMul
local instance aModule : Module R (A c):=Algebra.toModule
local instance baseAlgebra : Algebra (A c) S:=(InfinityGlobalBase318.sourceBaseMap c).toAlgebra
local instance baseTower : IsScalarTower R (A c) S:=
  IsScalarTower.of_algebraMap_eq (fun p=>(InfinityGlobalBase318.sourceBaseMap_polynomial c p).symm)

/-- This equivalence retains the reciprocal polynomial map s ↦ t⁻¹. -/
@[expose] def reciprocalBaseEquiv : ContactReciprocalBase318.Base≃ₐ[R]S:=
  { ContactReciprocalBase318.reciprocalEquiv.symm with
    commutes':=ContactReciprocalBase318.backward_map }

local instance fullLocalization : IsLocalization.Away ContactReciprocalBase318.denominator S:=
  IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers ContactReciprocalBase318.denominator) reciprocalBaseEquiv

/-- The original whole unbranched base is precisely the reciprocal open
with its reciprocal coordinate inverted. -/
theorem sourceBase_isLocalization :
    IsLocalization.Away (algebraMap R (A c) X) S:=by
  letI:IsLocalization.Away (X*ReciprocalInfinityBase318.reciprocalDenominator c) S:=by
    apply IsLocalization.Away.of_associated (r:=ContactReciprocalBase318.denominator)
    refine ⟨(Units.map (C:ℚ→+*R) (Units.mk0 (scalar c) (scalar_ne_zero c))),?_⟩
    change ContactReciprocalBase318.denominator*C (scalar c)=_
    rw [denominator_identity,mul_comm]
  exact away_of_mul X (ReciprocalInfinityBase318.reciprocalDenominator c)
end ReciprocalOverlapBase318
