module
public import FourRootFullFiniteInertia318
public import FourRootAffineSmooth318
public import Mathlib.NumberTheory.RamificationInertia.Galois
public section
noncomputable section
namespace FourRootActualOrderGalois318
open FourRootActualGenericField318 FourRootAffineTensorPresentation318 FourRootActualFractionField318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance polyAlgebra:Algebra P (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance rawAlgebra:Algebra (A b) (L b):=(affineEmbedding b).toAlgebra
/-- Retain the native tensor scalar action instead of installing a competing
P-algebra dictionary. Its map is the SAME original unshifted base composite. -/
lemma base_algebraMap (p:P):algebraMap P (L b) p=
    algebraMap K (L b) (algebraMap P K p):=
  IsScalarTower.algebraMap_apply P K (L b) p
local instance affineTower:IsScalarTower P (A b) (L b):=
  IsScalarTower.of_algebraMap_eq (R:=P) (S:=A b) (A:=L b)
    (fun p=>(base_algebraMap b p).trans (embedding_on_polynomial b p).symm)

lemma finite_free:Module.Finite P (A b)∧Module.Free P (A b):=by
  letI:Module.Finite P (TensorRing b):=(FourRootOrder318.finite_free (radicand b)).1
  letI:Module.Free P (TensorRing b):=(FourRootOrder318.finite_free (radicand b)).2
  exact ⟨Module.Finite.equiv (polynomialEquivalence b).symm.toLinearEquiv,
    Module.Free.of_equiv (polynomialEquivalence b).symm.toLinearEquiv⟩
local instance affineFinite:Module.Finite P (A b):=(finite_free b).1
local instance affineFree:Module.Free P (A b):=(finite_free b).2

include hb in
/-- The entire actual finite polynomial quotient is the integral closure
of the SAME unshifted C[t] in its specified full sixteen-degree field. -/
theorem integralClosure:IsIntegralClosure (A b) P (L b):=by
  letI:Fact (QuadraticTower318.Independent (parameter b)):=⟨independent b hb⟩
  letI:IsDomain (A b):=affine_domain b hb
  letI:IsFractionRing (A b) (L b):=actual_fractionField b hb
  letI:=FourRootAffineSmooth318.integrallyClosed b hb
  constructor
  · exact affineEmbedding_injective b
  · intro x
    constructor
    · intro hx
      exact IsIntegrallyClosed.algebraMap_eq_of_integral (hx.tower_top:IsIntegral (A b) x)
    · rintro ⟨y,rfl⟩
      exact (IsIntegral.of_finite P y).map (IsScalarTower.toAlgHom P (A b) (L b))

abbrev G:=A b≃ₐ[P]A b
include hb in
lemma group_finite:Finite (G b):=
  Finite.of_equiv FourBinaryCharacters318.Group (FourRootActualOrderAutomorphisms318.signEquivalence b hb)
include hb in
theorem invariant:Algebra.IsInvariant P (A b) (G b):=by
  letI:Fact (QuadraticTower318.Independent (parameter b)):=⟨independent b hb⟩
  letI:IsDomain (A b):=affine_domain b hb
  letI:IsFractionRing (A b) (L b):=actual_fractionField b hb
  letI:IsIntegralClosure (A b) P (L b):=integralClosure b hb
  letI:FiniteDimensional K (L b):=
    Module.finite_of_finrank_pos (by rw [actual_degree b hb];decide)
  letI:IsGalois K (L b):=ActualKummerGalois318.raw_galois (parameter b)
  exact Algebra.isInvariant_of_isGalois' P K (L b) (A b)
include hb in
theorem galoisGroup:IsGaloisGroup (G b) P (A b) where
  faithful:=inferInstance
  commutes:=inferInstance
  isInvariant:=invariant b hb
theorem finite_flat:Module.Finite P (A b)∧Module.Flat P (A b):=
  ⟨inferInstance,Module.Flat.of_free⟩
end FourRootActualOrderGalois318
