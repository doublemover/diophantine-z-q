module
public import NormalizedCotangentEvaluation318
public section
noncomputable section
namespace NormalizedReciprocalParameter318
open Polynomial FirstOrderCotangentEvaluation318
open scoped TensorProduct
variable (V K : Type*) [CommRing V] [Field K] [CharZero K] [Algebra V K]

/-- Change only the first-order parameter, not the underlying point or any
root sign. This is a genuine algebra homomorphism of the first-order ring. -/
@[expose] def rescale (b : K) : TrivSqZeroExt K K →ₐ[K] TrivSqZeroExt K K :=
  TrivSqZeroExt.map (b • (LinearMap.id : K →ₗ[K] K))

@[simp] theorem rescale_fst (b : K) (x : TrivSqZeroExt K K) :
    (rescale K b x).fst=x.fst := by
  simp only [rescale,TrivSqZeroExt.fst_map]

@[simp] theorem rescale_snd (b : K) (x : TrivSqZeroExt K K) :
    (rescale K b x).snd=b*x.snd := by
  simp only [rescale,TrivSqZeroExt.snd_map,LinearMap.smul_apply,
    LinearMap.id_apply,smul_eq_mul]

/-- The exact chain-rule scalar for w=1/t. No assertion that this scalar
is integral or an integral unit is made, including at bad finite places. -/
@[expose] def factor (t : K) : K := -(t⁻¹)^2

theorem factor_ne (t : K) (ht : t≠0) : factor K t≠0 :=
  neg_ne_zero.mpr (pow_ne_zero 2 (inv_ne_zero ht))

theorem factor_square (t : K) : (factor K t)^2=(t⁻¹)^4 := by
  unfold factor
  ring

variable (d a : Fin 4 → V) (t : K)
local notation "A" => DVRNormalizedInfinityOrder318.Order V d a
local notation "p" => DVRNormalizedInfinityOrder318.coefficient V d a
variable (f : A →ₐ[V] V)
  (hf : ∀ q : V[X],fieldPoint V A K f (algebraMap V[X] A q)=Polynomial.aeval t⁻¹ q)
  (hn : ∀ i,fieldPoint V A K f (FourRootOrderSigns318.generator p i)≠0)

/-- The SAME whole reciprocal order and integral point, now differentiated
with respect to the original parameter t. No dense-open quotient, alternate
point, generic derivation, or chosen square roots are supplied. -/
@[expose] def jet : A →ₐ[V] TrivSqZeroExt K K :=
  ((rescale K (factor K t)).restrictScalars V).comp
    (NormalizedCotangentEvaluation318.infinityJet V K d a t⁻¹ f hf hn)

theorem jet_projection (x : A) :
    (jet V K d a t f hf hn x).fst=fieldPoint V A K f x := by
  change (rescale K (factor K t)
    (NormalizedCotangentEvaluation318.infinityJet V K d a t⁻¹ f hf hn x)).fst=_
  rw [rescale_fst,NormalizedCotangentEvaluation318.infinityJet_projection]

theorem jet_coordinate :
    jet V K d a t f hf hn (algebraMap V[X] A X)=
      (t⁻¹,factor K t) := by
  change rescale K (factor K t)
    (FourRootFirstOrderPoint318.lift V K p t⁻¹ _ _ (algebraMap V[X] A X))=_
  rw [FourRootFirstOrderPoint318.lift_polynomial,Polynomial.aeval_X]
  apply TrivSqZeroExt.ext
  · rw [rescale_fst]
    rfl
  · rw [rescale_snd]
    change factor K t*1=factor K t
    exact mul_one _

/-- The computed reciprocal jet is the multiplicative inverse of t+epsilon.
Thus its scalar is justified by the coordinate identity, not a label. -/
theorem parameter_product (ht : t≠0) :
    FourRootFirstOrderPoint318.parameter K t *
      jet V K d a t f hf hn (algebraMap V[X] A X)=1 := by
  rw [jet_coordinate]
  apply TrivSqZeroExt.ext
  · change t*t⁻¹=1
    exact mul_inv_cancel₀ ht
  · change t*(-(t⁻¹)^2)+1*t⁻¹=0
    field_simp [ht]
    <;> ring

/-- Native universal cotangent evaluation extracted from this constructed
original-parameter jet at the fixed point f. -/
@[expose] def evaluation :
    letI : Algebra A V := f.toRingHom.toAlgebra
    V ⊗[A] KaehlerDifferential V A →ₗ[V] K :=
  integralFiberMap V A K f (jet V K d a t f hf hn)
    (jet_projection V K d a t f hf hn)

/-- Exact comparison on every integral differential generator, not just
on the coordinate or on a selected one-dimensional abstract space. -/
theorem evaluation_differential (x : A) :
    letI : Algebra A V := f.toRingHom.toAlgebra
    evaluation V K d a t f hf hn ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A x)=
      factor K t * NormalizedCotangentEvaluation318.infinityEvaluation V K d a t⁻¹ f hf hn
        ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A x) := by
  letI : Algebra A V := f.toRingHom.toAlgebra
  rw [evaluation,integralFiberMap_differential,
    NormalizedCotangentEvaluation318.infinityEvaluation,integralFiberMap_differential]
  exact rescale_snd K (factor K t) _

theorem evaluation_coordinate :
    letI : Algebra A V := f.toRingHom.toAlgebra
    evaluation V K d a t f hf hn
      ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A (algebraMap V[X] A X))=factor K t := by
  letI : Algebra A V := f.toRingHom.toAlgebra
  rw [evaluation_differential,NormalizedCotangentEvaluation318.infinityEvaluation_dX,mul_one]

/-- Each signed normalized root keeps its actual point value. Its derivative
has both the reciprocal polynomial derivative and the original t factor. -/
theorem evaluation_root (i : Fin 4) :
    letI : Algebra A V := f.toRingHom.toAlgebra
    evaluation V K d a t f hf hn
      ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A (FourRootOrderSigns318.generator p i))=
      factor K t * (algebraMap V K (d i)*(1-2*algebraMap V K (a i)*t⁻¹) /
        (2*NormalizedCotangentEvaluation318.infinityRoots V K d a f i)) := by
  letI : Algebra A V := f.toRingHom.toAlgebra
  rw [evaluation,integralFiberMap_differential]
  change (rescale K (factor K t)
    (FourRootFirstOrderPoint318.lift V K p t⁻¹ _ _
      (FourRootOrderSigns318.generator p i))).snd=_
  rw [rescale_snd,FourRootFirstOrderPoint318.lift_root]
  rfl

/-- On quadratic pure differentials the exact scalar is t^-4, not t^-2.
This is an evaluation identity, not equality of integral image lattices. -/
theorem quadratic_differentials (x y : A) :
    letI : Algebra A V := f.toRingHom.toAlgebra
    evaluation V K d a t f hf hn ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A x) *
      evaluation V K d a t f hf hn ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A y)=
      (t⁻¹)^4 *
        (NormalizedCotangentEvaluation318.infinityEvaluation V K d a t⁻¹ f hf hn
          ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A x) *
         NormalizedCotangentEvaluation318.infinityEvaluation V K d a t⁻¹ f hf hn
          ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A y)) := by
  letI : Algebra A V := f.toRingHom.toAlgebra
  rw [evaluation_differential,evaluation_differential]
  unfold factor
  ring
end NormalizedReciprocalParameter318
