module
public import NormalizedFirstOrderPoints318
public import FirstOrderCotangentEvaluation318
public section
noncomputable section
namespace NormalizedCotangentEvaluation318
open Polynomial FirstOrderCotangentEvaluation318
open scoped TensorProduct
variable (V K : Type*) [CommRing V] [Field K] [CharZero K] [Algebra V K]
  (d a : Fin 4 → V) (t : K)

section Finite
local notation "A" => DVRNormalizedFiniteOrder318.Order V d a
local notation "p" => DVRNormalizedFiniteOrder318.coefficient V d a
variable (f : A →ₐ[V] V)
  (hf : ∀ q : V[X],fieldPoint V A K f (algebraMap V[X] A q)=Polynomial.aeval t q)
  (hn : ∀ i,fieldPoint V A K f (FourRootOrderSigns318.generator p i)≠0)

@[expose] def finiteRoots (i : Fin 4) : K :=
  fieldPoint V A K f (FourRootOrderSigns318.generator p i)

theorem finiteRoots_square (i : Fin 4) :
    (finiteRoots V K d a f i)^2=algebraMap V K (d i)*(t-algebraMap V K (a i)) := by
  have h := congrArg (fieldPoint V A K f) (FourRootOrderSigns318.generator_square p i)
  simpa only [map_pow,hf,DVRNormalizedFiniteOrder318.coefficient,map_mul,map_sub,
    Polynomial.aeval_C,Polynomial.aeval_X,finiteRoots] using h

@[expose] def finiteJet : A →ₐ[V] TrivSqZeroExt K K :=
  NormalizedFirstOrderPoints318.finiteLift V K d a t (finiteRoots V K d a f) hn
    (finiteRoots_square V K d a t f hf)

theorem finiteJet_projection (x : A) :
    (finiteJet V K d a t f hf hn x).fst=fieldPoint V A K f x := by
  have h := FourRootFirstOrderPoint318.projection_eq V K p t
    (fun i => FourRootFirstOrderPoint318.rootJet K (finiteRoots V K d a f i) (algebraMap V K (d i)))
    (NormalizedFirstOrderPoints318.finite_relation V K d a t (finiteRoots V K d a f) hn
      (finiteRoots_square V K d a t f hf))
    (fieldPoint V A K f).toRingHom hf (fun _ => rfl)
  exact RingHom.congr_fun h x

/-- Construct the missing evaluation functional on the actual integral
finite-chart cotangent pullback, from its actual point and nonzero roots.
No derivation, generic frame or cotangent functional is assumed. -/
@[expose] def finiteEvaluation :
    letI : Algebra A V := f.toRingHom.toAlgebra
    V ⊗[A] KaehlerDifferential V A →ₗ[V] K :=
  integralFiberMap V A K f (finiteJet V K d a t f hf hn)
    (finiteJet_projection V K d a t f hf hn)

theorem finiteEvaluation_dX :
    letI : Algebra A V := f.toRingHom.toAlgebra
    finiteEvaluation V K d a t f hf hn
      ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A (algebraMap V[X] A X))=1 := by
  letI : Algebra A V := f.toRingHom.toAlgebra
  rw [finiteEvaluation,integralFiberMap_differential]
  change (FourRootFirstOrderPoint318.lift V K p t _ _ (algebraMap V[X] A X)).snd=1
  rw [FourRootFirstOrderPoint318.lift_polynomial,Polynomial.aeval_X]
  rfl
end Finite

section Infinity
local notation "A" => DVRNormalizedInfinityOrder318.Order V d a
local notation "p" => DVRNormalizedInfinityOrder318.coefficient V d a
variable (f : A →ₐ[V] V)
  (hf : ∀ q : V[X],fieldPoint V A K f (algebraMap V[X] A q)=Polynomial.aeval t q)
  (hn : ∀ i,fieldPoint V A K f (FourRootOrderSigns318.generator p i)≠0)

@[expose] def infinityRoots (i : Fin 4) : K :=
  fieldPoint V A K f (FourRootOrderSigns318.generator p i)

theorem infinityRoots_square (i : Fin 4) :
    (infinityRoots V K d a f i)^2=algebraMap V K (d i)*t*(1-algebraMap V K (a i)*t) := by
  have h := congrArg (fieldPoint V A K f) (FourRootOrderSigns318.generator_square p i)
  simpa only [map_pow,hf,DVRNormalizedInfinityOrder318.coefficient,map_mul,map_sub,map_one,
    Polynomial.aeval_C,Polynomial.aeval_X,infinityRoots] using h

@[expose] def infinityJet : A →ₐ[V] TrivSqZeroExt K K :=
  NormalizedFirstOrderPoints318.infinityLift V K d a t (infinityRoots V K d a f) hn
    (infinityRoots_square V K d a t f hf)

theorem infinityJet_projection (x : A) :
    (infinityJet V K d a t f hf hn x).fst=fieldPoint V A K f x := by
  have h := FourRootFirstOrderPoint318.projection_eq V K p t
    (fun i => FourRootFirstOrderPoint318.rootJet K (infinityRoots V K d a f i)
      (algebraMap V K (d i)*(1-2*algebraMap V K (a i)*t)))
    (NormalizedFirstOrderPoints318.infinity_relation V K d a t (infinityRoots V K d a f) hn
      (infinityRoots_square V K d a t f hf))
    (fieldPoint V A K f).toRingHom hf (fun _ => rfl)
  exact RingHom.congr_fun h x

/-- Genuine reciprocal-chart functional, normalized by Dw=1. It is NOT
identified with the original Dt-normalized rational frame. -/
@[expose] def infinityEvaluation :
    letI : Algebra A V := f.toRingHom.toAlgebra
    V ⊗[A] KaehlerDifferential V A →ₗ[V] K :=
  integralFiberMap V A K f (infinityJet V K d a t f hf hn)
    (infinityJet_projection V K d a t f hf hn)

theorem infinityEvaluation_dX :
    letI : Algebra A V := f.toRingHom.toAlgebra
    infinityEvaluation V K d a t f hf hn
      ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A (algebraMap V[X] A X))=1 := by
  letI : Algebra A V := f.toRingHom.toAlgebra
  rw [infinityEvaluation,integralFiberMap_differential]
  change (FourRootFirstOrderPoint318.lift V K p t _ _ (algebraMap V[X] A X)).snd=1
  rw [FourRootFirstOrderPoint318.lift_polynomial,Polynomial.aeval_X]
  rfl
end Infinity
end NormalizedCotangentEvaluation318
